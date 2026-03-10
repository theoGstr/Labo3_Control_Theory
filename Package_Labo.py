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