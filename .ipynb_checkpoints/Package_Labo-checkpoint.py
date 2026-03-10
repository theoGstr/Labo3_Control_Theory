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
    
    # Vérification de sécurité : s'assurer qu'il y a des données d'entrée
    if len(SP) == 0 or len(PV) == 0:
        return

    # Récupération des valeurs actuelles (k) depuis la fin des vecteurs
    sp_k = SP[-1]
    pv_k = PV[-1]
    man_k = Man[-1]
    mv_man_k = MVMan[-1]
    mv_ff_k = MVFF[-1]

    # 1. Initialisation de l'Erreur (E)
    e_k = sp_k - pv_k

    # 2. Calcul de la partie proportionnelle (MVP)
    mv_p_k = Kc * e_k

    # --- Gestion des valeurs précédentes (k-1) pour le calcul I et D ---
    if len(E) == 0: # Si c'est la toute première exécution de la boucle
        e_k_1 = sp_k - PVInit
        mvi_k_1 = 0.0
        mvd_k_1 = 0.0
    else:
        e_k_1 = E[-1]
        mvi_k_1 = MVI[-1]
        mvd_k_1 = MVD[-1]

    # Parsing des méthodes de discrétisation
    method_I, method_D = method.split('-')

    # 3. Calcul de la partie intégrale (MVI)
    if Ti > 0:
        if method_I == 'EBD':
            mv_i_k = mvi_k_1 + (Kc * Ts / Ti) * e_k
        elif method_I == 'TRAP':
            mv_i_k = mvi_k_1 + (Kc * Ts / (2 * Ti)) * (e_k + e_k_1)
        else:
            mv_i_k = mvi_k_1
    else:
        mv_i_k = 0.0

    # 4. Calcul de la partie dérivée (MVD) avec filtre
    if Td > 0:
        Tfd = alpha * Td  # Constante de temps du filtre dérivé
        if method_D == 'EBD':
            mv_d_k = (Tfd / (Tfd + Ts)) * mvd_k_1 + (Kc * Td / (Tfd + Ts)) * (e_k - e_k_1)
        elif method_D == 'TRAP':
            mv_d_k = ((Tfd - Ts/2) / (Tfd + Ts/2)) * mvd_k_1 + (Kc * Td / (Tfd + Ts/2)) * (e_k - e_k_1)
        else:
            mv_d_k = 0.0
    else:
        mv_d_k = 0.0

    # 5. Gestion du mode Manuel (Man) et de son reset d'Intégrale
    if man_k:
        if ManFF:
            # Si le FeedForward est activé en manuel : MV = MVMan + MVFF
            mv_i_k = mv_man_k - mv_p_k - mv_d_k
        else:
            # Mode manuel standard : MV = MVMan
            mv_i_k = mv_man_k - mv_p_k - mv_d_k - mv_ff_k

    # 6. Gestion de la Saturation (Anti-windup)
    # Le calcul anti-windup s'applique uniquement si on n'est PAS en mode manuel
    elif not man_k:
        mv_temp = mv_p_k + mv_i_k + mv_d_k + mv_ff_k
        if mv_temp > MVMax:
            mv_i_k = MVMax - mv_p_k - mv_d_k - mv_ff_k
        elif mv_temp < MVMin:
            mv_i_k = MVMin - mv_p_k - mv_d_k - mv_ff_k

    # 7. Calcul final de MV
    mv_k = mv_p_k + mv_i_k + mv_d_k + mv_ff_k

    # Double sécurité : forcer la saturation finale des limites
    if mv_k > MVMax:
        mv_k = MVMax
    elif mv_k < MVMin:
        mv_k = MVMin

    # --- Ajout (Append) des nouvelles valeurs calculées aux vecteurs ---
    E.append(e_k)
    MVP.append(mv_p_k)
    MVI.append(mv_i_k)
    MVD.append(mv_d_k)
    MV.append(mv_k)