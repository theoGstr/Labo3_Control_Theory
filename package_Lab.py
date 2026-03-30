import numpy as np

import matplotlib.pyplot as plt

#-----------------------------------        
def LL_RT(MV,Kp,Tlag,Tlead,Ts,PV,PVInit=0,method='EBD'):
    
    """
    The function "FO_RT" needs to be included in a "for or while loop".
    
    :MV: input vector
    :Kp: process gain
    :Tlag: lag time constant [s]
    :Tlead: lag time constant [s]
    :Ts: sampling period [s]
    :PV: output vector
    :PVInit: (optional: default value is 0)
    :method: discretisation method (optional: default value is 'EBD')
        EBD: Euler Backward difference
        EFD: Euler Forward difference
        TRAP: Trapezoïdal method
    
    The function "FO_RT" appends a value to the output vector "PV".
    The appended value is obtained from a recurrent equation that depends on the discretisation method.
    """    
    
    if (Tlag != 0):
        K = float(Ts)/Tlag
        if len(PV) == 0:
            PV.append(PVInit)
        else: # MV[k+1] is MV[-1] and MV[k] is MV[-2]
            if method == 'EBD':
                #PV.append(1/(1+K)*PV[len(PV)-1]+((Kp*K)/(1+K))*((1+Tlead/Ts)*MV[-1]-Tlead/Ts*MV[0]))
                PV.append((1/(1+K)) * PV[-1] + ((Kp*K)/(1+K)) * ((1 + Tlead/Ts) * MV[-1] - (Tlead/Ts) * MV[-2]))
            elif method == 'EFD':
                PV.append((1-K) * PV[-1] + (Kp*K) * ((Tlead/Ts) * MV[-1] + (1-Tlead/Ts) * MV[-2]))
            elif method == 'TRAP':
                PV.append(((2 - K) / (2 + K)) * PV[-1] + (Kp * K / (2 + K)) * ((2*Tlead/Ts + 1) * MV[-1] + (1 - 2*Tlead/Ts) * MV[-2]))
            else:
                PV.append((1/(1+K))*PV[-1] + (K*Kp/(1+K))*MV[-1])
    else:
        PV.append(Kp*MV[-1])


#-----------------------------------        
def PID_RT(SP, PV, Man, MVMan, MVFF, Kc, Ti, Td, alpha, Ts, 
           MVMin, MVMax, MV, MVP, MVI, MVD, E, 
           ManFF=False, PVInit=0, method='EBD'):
    """
    Real-time PID controller with feedforward, manual mode, and anti wind-up.
    
    Key design choice — anti wind-up excludes MVD:
        MVI_reset = MV_sat - MVP - MVFF   (MVD intentionally excluded)
    MVD is a transient term that decays on its own. Including it in the reset
    causes MVI to jump violently at SP steps, producing an unwanted MV bump.
    The final MV output is hard-clamped to [MVMin, MVMax] instead.
    """

    # 1. Error calculation
    # If PV is empty (initial step), use PVInit to calculate the first error
    if len(PV) == 0:
        E.append(SP[-1] - PVInit)
    else:
        E.append(SP[-1] - PV[-1])

    # 2. Proportional Term (MVP)
    MVP.append(Kc * E[-1])

    # 3. Integral Term (MVI)
    # The first execution always uses EBD (Euler Backward) to initialize
    if Ti > 0:
        if len(MVI) == 0:
            MVI.append((Kc * Ts / Ti) * E[-1])
        elif method== 'TRAP':
            MVI.append(MVI[-1] + (0.5 * Kc * Ts / Ti) * (E[-1] + E[-2]))
        else: # Default to EBD
            MVI.append(MVI[-1] + (Kc * Ts / Ti) * E[-1])
    else:
        MVI.append(0.0)

    # 4. Derivative Term (MVD) with filter (alpha)
    if Td > 0 and alpha > 0:
        Tfd = alpha * Td
        if len(MVD) == 0:
            MVD.append(0.0)
        elif method == 'TRAP':
            MVD.append(((Tfd - Ts/2) / (Tfd + Ts/2)) * MVD[-1] + (Kc * Td / (Tfd + Ts/2)) * (E[-1] - E[-2]))
        else: # Default to EBD
            MVD.append((Tfd / (Tfd + Ts)) * MVD[-1] + (Kc * Td / (Tfd + Ts)) * (E[-1] - E[-2]))
    else:
        MVD.append(0.0)

    # 5. Manual Mode Handling (Bumpless Transfer)
    # In manual mode, we force the Integrator so that MVP + MVI + MVD + MVFF = MVMan
    if Man[-1] == True:
        if ManFF:
            MVI[-1] = MVMan[-1] - MVP[-1] - MVD[-1]
        else:
            MVI[-1] = MVMan[-1] - MVP[-1] - MVD[-1] - MVFF[-1]

    # 6. Anti Wind-Up Logic (Automatic Mode)
    else:
        mv_temp = MVP[-1] + MVI[-1] + MVD[-1] + MVFF[-1]
        
        # If output saturates, we reset MVI to the limit MINUS Proportional and FF.
        # Rationale: Excluding MVD keeps MVI smooth and monotonic during SP steps.
        if mv_temp > MVMax:
            MVI[-1] = MVMax - MVP[-1] - MVFF[-1]
        elif mv_temp < MVMin:
            MVI[-1] = MVMin - MVP[-1] - MVFF[-1]

    # 7. Final Output Calculation & Hard Clamp
    # The hard clamp ensures the physical actuator limits are respected 
    # even when MVD spikes.
    mv_k = MVP[-1] + MVI[-1] + MVD[-1] + MVFF[-1]
    MV.append(max(MVMin, min(MVMax, mv_k)))


def IMC_tuning(K, T1, T2, theta, gamma):
    """
    Calcule les paramètres d'un régulateur PID en utilisant la méthode IMC (Internal Model Control).
    
    Arguments:
    K     -- Gain statique du procédé
    T1    -- Constante de temps principale [s]
    T2    -- Deuxième constante de temps [s]
    theta -- Retard pur (dead time) [s]
    gamma -- Facteur d'agressivité (tau_c = gamma * T1). 
             Plus gamma est petit (< 1), plus le réglage est agressif.
    
    Retourne:
    Kc, Ti, Td -- Gains proportionnel, intégral et dérivé pour le PID
    """

    tau_c = gamma * T1 
    
    # Formules IMC pour SOPDT (Série -> Parallèle conversion)
    Kc = (T1 + T2) / (K * (tau_c + theta))
    Ti = T1 + T2
    Td = (T1 * T2) / (T1 + T2)
    
    return Kc, Ti, Td