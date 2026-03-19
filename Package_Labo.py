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
    The function "PID_RT" needs to be included in a "for or while loop".

    :SP:     SP (or SetPoint) vector
    :PV:     PV (or Process Value) vector
    :Man:    Man (or Manual controller mode) vector (True or False)
    :MVMan:  MVMan (or Manual value for MV) vector
    :MVFF:   MVFF (or FeedForward) vector

    :Kc:     controller gain
    :Ti:     Integral time constant [s]
    :Td:     derivative time constant [s]
    :alpha:  Tfd = alpha*Td where Tfd is the derivative filter time constant [s]
    :Ts:     sampling period [s]

    :MVMin:  minimum value for MV (used for saturation and anti wind-up)
    :MVMax:  maximum value for MV (used for saturation and anti wind-up)

    :MV:     MV (or Manipulated Value) vector
    :MVP:    MVP (or Proportional part of MV) vector
    :MVI:    MVI (or Integral part of MV) vector
    :MVD:    MVD (or Derivative part of MV) vector
    :E:      E (or control Error) vector

    :ManFF:  Activated FF in manual mode (optional: default boolean value is False)
    :PVInit: Initial value for PV (optional: default value is 0);
             used if PID_RT is run first in the sequence and no value of PV is available yet.
    :method: discretisation method (optional: default value is 'EBD-EBD')
             EBD-EBD: EBD for integral action and EBD for derivative action
             EBD-TRAP: EBD integral action and TRAP for derivative action
             TRAP-EBD: TRAP for integral action and EBD for derivative action
             TRAP-TRAP: TRAP for integral action and TRAP for derivative action

    The function "PID_RT" appends new values to the vectors "MV", "MVP", "MVI", and "MVD".
    The appended values are based on the PID algorithm, the controller mode, and feedforward.
    Note that saturation of "MV" within the limits [MVMin MVMax] is implemented with anti wind-up.
    """

    # Parse discretisation methods
    method_I, method_D = method.split('-')

    # -------------------------------------------------------------------------
    # 1. Initialisation of E  (append first, then use E[-1], E[-2])
    # -------------------------------------------------------------------------
    if len(PV) == 0:
        E.append(SP[-1] - PVInit)
    else:
        E.append(SP[-1] - PV[-1])

    # -------------------------------------------------------------------------
    # 2. Compute MVP (proportional part) and append
    # -------------------------------------------------------------------------
    MVP.append(Kc * E[-1])

    # -------------------------------------------------------------------------
    # 3. Compute MVI (integral part) and append
    #    - First call: always initialise with EBD
    #    - Subsequent calls: use chosen method (TRAP or EBD)
    # -------------------------------------------------------------------------
    if Ti > 0:
        if len(MVI) == 0:
            # Initialisation: always EBD on very first step
            MVI.append((Kc * Ts / Ti) * E[-1])
        else:
            if method_I == 'TRAP':
                MVI.append(MVI[-1] + (0.5 * Kc * Ts / Ti) * (E[-1] + E[-2]))
            else:  # EBD (default)
                MVI.append(MVI[-1] + (Kc * Ts / Ti) * E[-1])
    else:
        MVI.append(0.0)

    # -------------------------------------------------------------------------
    # 4. Compute MVD (derivative part with filter) and append
    # -------------------------------------------------------------------------
    if Td > 0 and alpha > 0:
        Tfd = alpha * Td
        if len(MVD) == 0:
            # Initialisation: no previous error available, derivative starts at 0
            MVD.append(0.0)
        else:
            if method_D == 'TRAP':
                MVD.append(
                    ((Tfd - Ts / 2) / (Tfd + Ts / 2)) * MVD[-1]
                    + (Kc * Td / (Tfd + Ts / 2)) * (E[-1] - E[-2])
                )
            else:  # EBD (default)
                MVD.append(
                    (Tfd / (Tfd + Ts)) * MVD[-1]
                    + (Kc * Td / (Tfd + Ts)) * (E[-1] - E[-2])
                )
    else:
        MVD.append(0.0)

    # -------------------------------------------------------------------------
    # 5. Integrator reset: Manual mode
    #    Modify MVI[-1] in place (no re-append — as shown by teacher's crossed APPEND)
    # -------------------------------------------------------------------------
    if Man[-1] == True:
        if ManFF:
            # MV = MVMan + MVFF  =>  MVI = MVMan - MVP - MVD
            MVI[-1] = MVMan[-1] - MVP[-1] - MVD[-1]
        else:
            # MV = MVMan  =>  MVI = MVMan - MVP - MVD - MVFF
            MVI[-1] = MVMan[-1] - MVP[-1] - MVD[-1] - MVFF[-1]

    # -------------------------------------------------------------------------
    # 6. Integrator reset: Actuator saturation (anti wind-up)
    #    Only applies in automatic mode
    # -------------------------------------------------------------------------
    else:
        mv_temp = MVP[-1] + MVI[-1] + MVD[-1] + MVFF[-1]
        if mv_temp > MVMax:
            MVI[-1] = MVMax - MVP[-1] - MVD[-1] - MVFF[-1]
        elif mv_temp < MVMin:
            MVI[-1] = MVMin - MVP[-1] - MVD[-1] - MVFF[-1]

    # -------------------------------------------------------------------------
    # 7. Compute final MV and append
    # -------------------------------------------------------------------------
    MV.append(MVP[-1] + MVI[-1] + MVD[-1] + MVFF[-1])