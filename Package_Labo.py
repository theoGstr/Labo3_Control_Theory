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
        K = Ts/Tlag
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
def PID_RT(SP, PV, Man, MVMan, MVFF, Kc, Ti, Td, alpha, Ts, MVMin, MVMax, MV, MVP, MVI, MVD, E, ManFF=False, PVInit=0, method='EBD-EBD'):
    
    """
    Calcule et ajoute les nouvelles valeurs d'un contrôleur PID en temps réel avec feedforward, 
    mode manuel et anti-windup (saturation).
    """
    
   

   
    methodI, methodD = method.split('-')
    Tfd = alpha * Td

    if len(PV) == 0:
        E.append(SP[-1] - PVInit)
    else:
        E.append(SP[-1] - PV[-1])

    MVP.append(Kc * E[-1])

    if Ti > 0:
        if len(MVI) == 0:
            MVI.append((Kc * Ts / Ti) * E[-1])
        else:
            if methodI == 'TRAP':
                MVI.append(MVI[-1] + (0.5 * Kc * Ts / Ti) * (E[-1] + E[-2]))
            else:
                MVI.append(MVI[-1] + (Kc * Ts / Ti) * E[-1])
    else:
        MVI.append(0.0)

    if Td > 0:
        if len(MVD) == 0:
            MVD.append(0.0)
        else:
            if methodD == 'EBD':
                MVD.append((Tfd / (Tfd + Ts)) * MVD[-1] + (Kc * Td / (Tfd + Ts)) * (E[-1] - E[-2]))
            elif methodD == 'TRAP':
                MVD.append(((Tfd - Ts / 2) / (Tfd + Ts / 2)) * MVD[-1] + (Kc * Td / (Tfd + Ts / 2)) * (E[-1] - E[-2]))
            else:
                MVD.append(0.0)
    else:
        MVD.append(0.0)

    if Man[-1] == True:
        if ManFF:
            MVI[-1] = MVMan[-1] - MVP[-1] - MVD[-1]
        else:
            MVI[-1] = MVMan[-1] - MVP[-1] - MVD[-1] - MVFF[-1]
    else:
        MV_temp = MVP[-1] + MVI[-1] + MVD[-1] + MVFF[-1]
        if MV_temp > MVMax:
            MVI[-1] = MVMax - MVP[-1] - MVD[-1] - MVFF[-1]
        elif MV_temp < MVMin:
            MVI[-1] = MVMin - MVP[-1] - MVD[-1] - MVFF[-1]

    MV_k = MVP[-1] + MVI[-1] + MVD[-1] + MVFF[-1]

    if MV_k > MVMax:
        MV_k = MVMax
    elif MV_k < MVMin:
        MV_k = MVMin

    MV.append(MV_k)