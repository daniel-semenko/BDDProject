import pyeda
from pyeda.inter import *
from functools import reduce

def edgetoBF(i, j):
    n = 0
    x_F = ""
    y_F = ""
    xBin = '{0:05b}'.format(i)
    yBin = '{0:05b}'.format(j)
    # iterate over the bits in binary i to create x_F
    # produces "x[i] & ".. to match pyEDA style expression and indexed vars
    for i in xBin:
        if int(i) == 0:
            x_F += f"~x[{n}] & "
        elif int(i) == 1:
            x_F += f"x[{n}] & "
        n += 1    

    # reset the index
    n = 0

    # iterate over the bits in binary j to formulate the y_F
    for i in yBin:
        
        if int(i) == 0:
            y_F += f"~y[{n}] & "
        elif int(i) == 1:
            y_F += f"y[{n}] & "
        
        n += 1  
    
    # pop the last 3 chars from the expressions
    x_F = x_F[:-3]
    y_F = y_F[:-3]

    # create a new Formula with both x and y expressions
    return f"({x_F}) & ({y_F})"


def nodetoBF(i):
    n = 0
    x_F = ""
    xBin = '{0:05b}'.format(i)

    for i in xBin:
        
        if int(i) == 0:
            x_F += f"~x[{n}] & "
        elif int(i) == 1:
            x_F += f"x[{n}] & "
        
        n += 1  

    x_F = x_F[:-3]

    return f"{x_F}"


def create_booleanFormula_List(iL):
    booleanFormula = ""

    for i in iL:
        booleanFormula +=  f"({i}) | "
    
    return expr(booleanFormula[:-3])

def my_compose(BDD1, BDD2):
    x = bddvars('x', 5)
    y = bddvars('y', 5)
    z = bddvars('z', 5)
    BDD1_composed = BDD1.compose({x[0]:z[0], x[1]:z[1], x[2]:z[2], x[3]:z[3], x[4]:z[4]})
    BDD2_composed = BDD1.compose({y[0]:z[0], y[1]:z[1], y[2]:z[2], y[3]:z[3], y[4]:z[4]})
    return (BDD1_composed & BDD2_composed).smoothing(z)

def my_compose2(BDD1, BDD2):
    x = bddvars('x', 5)
    y = bddvars('y', 5)
    z = bddvars('z', 5)
    BDD1_composed = BDD1.compose({x[0]:z[0], x[1]:z[1], x[2]:z[2], x[3]:z[3], x[4]:z[4]})
    BDD2_composed = BDD1.compose({y[0]:z[0], y[1]:z[1], y[2]:z[2], y[3]:z[3], y[4]:z[4]})
    return (BDD1_composed & BDD2_composed)
    

def main():
    print("Creating graph G...")
    G = {}
    for i in range(0,32):
        G[i] = []

    print("G: {}".format(G))
    print("Done!\n")

    print("Creating set R, filling graph G...")
    R = []
    for i in range(0,32):
        for j in range(0,32):
            if ( (i+3)%32 == j%32 ) or ( (i+8)%32 == j%32 ):                          # iff => both true or both false => check for equality
                G[i].append(j)
                R_input = edgetoBF(i, j)
                R.append(R_input)
    print("G: {}\n".format(G))
    print("R: {}\n".format(R))
    print("Done!\n")
    
    print("Creating sets even and prime...")
    even = []
    for i in [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]:
        nF = nodetoBF(i)
        even.append(nF)

    prime = []
    for i in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        nF = nodetoBF(i)
        prime.append(nF)
    print("even: {}\n".format(even))
    print("prime: {}\n".format(prime))
    print("Done!\n")

    print("Creating Boolean Functions for even, prime, and R")
    BOOL_FUNC_EVEN = create_booleanFormula_List(even)
    BOOL_FUNC_PRIME = create_booleanFormula_List(prime)
    BOOL_FUNC_RR= create_booleanFormula_List(R)
    print("BOOL_FUNC_EVEN: {}\n".format(BOOL_FUNC_EVEN))
    print("BOOL_FUNC_PRIME: {}\n".format(BOOL_FUNC_PRIME))
    print("BOOL_FUNC_RR: {}\n".format(BOOL_FUNC_RR))
    print("Done!\n")




    ## STEP 3.1 - Obtain BDD's RR, EVEN, PRIME
    print("Creating BDDs for EVEN, PRIME, and R...")
    BDD_EVEN = expr2bdd(BOOL_FUNC_EVEN)     # BDD over 5 BDD Variables yy1,...,yy5
    BDD_PRIME = expr2bdd(BOOL_FUNC_PRIME)   # BDD over 5 BDD Variables xx1,...,xx5
    BDD_RR = expr2bdd(BOOL_FUNC_RR)          # BDD over 10 BDD Variables xx1,...,xx5;yy1,...,yy5
    print("(BDD_EVEN): {}".format(BDD_EVEN))
    print("(BDD_PRIME): {}".format((BDD_PRIME)))
    print("(BDD_RR): {}".format((BDD_RR)))
    print("Done!\n")





    ## STEP 3.2 - COMPUTE BDD RR2 , herin RR2 encodes the set of node pairs such that one can reach the other in an even number of sets
    print("Computing the composition of BDD_RR and BDD_RR, RR2...")
    BDD_RR2 = my_compose(BDD_RR, BDD_RR)
    
    print("(BDD_RR2): {}".format((BDD_RR2)))
    print("bdd2expr(BDD_RR2): {}".format(bdd2expr(BDD_RR2)))
    print("Done!\n")


    ## STEP 3.3 compute BDD_RR2star
    print("Computing the transitive closure of RR2, RR2*...")

    H = BDD_RR2
    while True:
        J = H
        H = J | my_compose2(J, BDD_RR2)
        if H.equivalent(J):
            break
    BDD_RR2star = H

    print("bdd2expr(BDD_RR2star): {}".format(bdd2expr(BDD_RR2star)))
    print("Done!\n")
    ## STEP 3.4 COMPUTE BDD_PE
    
    print("Computing BDD PE...")
    BDD_PE = BDD_EVEN & BDD_PRIME & BDD_RR2star
    print("bdd2expr(BDD_PE): {}".format(bdd2expr(BDD_PE)))
    print("Done!\n")

    # STEP 3.5
    print("For each node u in [prime], is there a node v in [even] such that u can reach v in an even number of steps?: {}".format(bdd2expr(BDD_PE) is True))