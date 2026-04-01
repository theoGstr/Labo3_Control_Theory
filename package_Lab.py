import numpy as np
import matplotlib.pyplot as plt
from package_DBR import Bode

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


def Margin(P, Cparams, omega, Show=True):
    """
    Calcule la margin de gain et la margin de phase pour analyser la robustesse du PID.
    
    Arguments:
    Ps      : Réponse en fréquence du procédé (obtenue via Bode)
    Cparams : Dictionnaire contenant les paramètres Kc, Ti, Td et alpha
    omega   : Vecteur de fréquence [rad/s]
    Show    : Affiche le diagramme de Bode avec les margins 

    Dependence: package_DBR Bode()
    """
    # 1. Calcul de la réponse du Procédé P(s)
    Ps = Bode(P, omega, Show=False)
    
    # 2. Initialisation des paramètres du Contrôleur
    s = 1j * omega
    Kc = Cparams['Kc']
    Ti = Cparams['Ti']
    Td = Cparams['Td']
    alpha = Cparams['alpha']
    Tfd = alpha * Td 
    
    # 3. Calcul du Controller Cs
    Cs = Kc * (1 + 1/(Ti * s) + (Td * s)/(Tfd * s + 1))
    
    # 4. Loop gain Ls = Ps * Cs
    Ls = Cs * Ps 
    
    # 5. Calcul des amplitudes et phases
    magdb = 20 * np.log10(np.abs(Ls))
    phasedeg = (180/np.pi) * np.unwrap(np.angle(Ls))

    # --- CALCUL DES marginS ---
    idxgc = np.argmin(np.abs(magdb)) 
    OmegaC = omega[idxgc]
    PhaseC = phasedeg[idxgc]
    MP = PhaseC + 180

    idxpc = np.argmin(np.abs(phasedeg + 180))
    OmegaU = omega[idxpc]
    GainUdb = magdb[idxpc]
    MG = -GainUdb
    # --- AFFICHAGE GRAPHIQUE ---
    if Show:
        fig, (axfreq, axtime) = plt.subplots(2, 1)
        fig.set_figheight(12)
        fig.set_figwidth(22)

        axfreq.semilogx(omega, magdb, label='L(s) = C(s)P(s)', color='blue', linewidth=2)
        axfreq.axhline(y=0, color='black', linestyle='-')
        axfreq.plot([OmegaU, OmegaU], [0, GainUdb], color='red', linestyle='--', linewidth=3, label=f'MG = {MG:.2f} dB')
        axfreq.set_xlim([np.min(omega), np.max(omega)])
        axfreq.set_ylim([np.min(magdb), np.max(magdb)]) 
        axfreq.set_ylabel('Amplitude |L| [dB]')
        axfreq.set_title('Diagramme de Bode de la Boucle Ouverte L(s)')
        axfreq.legend(loc='best')
        axfreq.grid(True, which="both", ls="-", alpha=0.5)

        axtime.semilogx(omega, phasedeg, label='L(s)', color='orange', linewidth=2)
        axtime.axhline(y=-180, color='black', linestyle='-')
        axtime.plot([OmegaC, OmegaC], [PhaseC, -180], color='green', linestyle='--', linewidth=3, label=f'MP = {MP:.2f}°')
        axtime.set_xlim([np.min(omega), np.max(omega)])
        axtime.set_ylim([np.max([np.min(phasedeg), -270]), np.max(phasedeg)])
        axtime.set_ylabel(r'Phase $\angle L$ [°]')
        axtime.set_xlabel(r'Fréquence $\omega$ [rad/s]')
        axtime.legend(loc='best')
        axtime.grid(True, which="both", ls="-", alpha=0.5)

        plt.tight_layout()
        plt.show()

    print(f'Gain margin : {MG:.2f} dB at the ultimate frequency : {OmegaU:.4f} rad/s')
    print(f'Phase margin : {MP:.2f}° at the crossover frequency : {OmegaC:.4f} rad/s')

    return MG, MP