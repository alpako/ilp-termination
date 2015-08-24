# -*- coding: utf-8 -*-

##!/usr/bin/env sage -python

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# imports #

import sys

from itertools import groupby
from functools import partial

import copy

from sage.all import *

import misc_matrix as MX

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# functions #


def formula_to_operands(formula):
    fe=formula.expand()
    return (fe.operator(),map(lambda m:(m.operator(),m.operands()), fe.operands()))

def to_number_direction(num):
    return (num/abs(num))


def sort_and_group_by_function (some_list, key_func):
    groups = []
    uniquekeys = []
    sorted_list = sorted(some_list, key=key_func)
    for k,v in groupby(sorted_list, key_func):
        groups.append(list(v))
        uniquekeys.append(k)
    return zip(uniquekeys,groups)

def group_eigenvalues_by_abs(vals):
    groups = sort_and_group_by_function(vals, abs)

    return map(lambda grp:(grp[0],map(to_number_direction,grp[1])), groups)
    # groups = []
    # uniquekeys = []
    # data = sorted(vals, key=abs)
    # for k, g in groupby(data, abs):
    #     # Store group iterator as a list
    #     groups.append(map(number_direction,list(g)))
    #     uniquekeys.append(k)
    # return zip(uniquekeys,groups)


def eigenvalue_superset_flat(evgroups):
    def handle_group(idx1,evgroup):
        (absval,dirvals) = evgroup
        evlist = [((idx1,0),absval,QQbar(1))]
        idx2=1
        for d in dirvals:
            if d != 1:
                evlist.append(((idx1,idx2), absval, d))
                idx2 += 1
        return evlist
    evsuperset=[]
    idx1=1
    for g in evgroups:
        evsuperset.extend(handle_group(idx1,g))
        idx1 += 1
    return evsuperset

def eigenvalue_superset(evgroups):
    def handle_group(evgroup):
        (absval,dirvals) = evgroup
        dirs = list(dirvals)
        if QQbar(1) not in dirvals:
            dirs.insert(0,QQbar(1))
        return (absval,dirs)

    evsuperset=[]
    for g in evgroups:
        evsuperset.append(handle_group(g))
    return evsuperset



# def find_jordan_block_dim_from_eigenvalue(jbs, ev_tuple):
#     dim=0
#     ev=ev_tuple[0]
#     for b in jbs:
#         d = b.dimensions()[0]
#         if ev == abs(b[0,0]) and d > dim:
#             dim = d
#     return dim
#
# def to_abstract_power_factors(jordan_matrix):
#     def handle_ev(abs_ds_tuple, max_block_size):
#         (absval,dirs) = abs_ds_tuple
#         fs=[]
#         for i in range(0,max_block_size):
#             fs.extend(map(lambda d: (absval,d,i), dirs))
#         return fs
#
#     evs = eigenvalue_superset(
#         group_eigenvalues_by_abs(
#         jordan_matrix.eigenvalues()))
#     jbs = MX.to_jordan_blocks(jordan_matrix)
#     abstract_factors = []
#     for ev in evs:
#         size = find_jordan_block_dim_from_eigenvalue(jbs,ev)
#         abstract_factors.extend(handle_ev(ev,size))
#     return abstract_factors



def group_entry_summands_by_eigenvalue(entry):
    smul=sage.symbolic.operators.mul_vararg
    sadd=sage.symbolic.operators.add_vararg
    def grp_key(summand):
        return (abs(summand[1][0][0]),summand[1][0][1])
        # (eigenvalue,power) -> (abs(eigenvalue), power)
    def norm_summand(summand):
        copysummand=(summand[0],summand[1][:])
        val = copysummand[1][0][0]
        pow = copysummand[1][0][1]
        if val != 0:
            copysummand[1][0]=(to_number_direction(val),pow)
        return copysummand
    def norm_summands(group):
        (k,vs)=group
        vs2=map(norm_summand, vs)
        return (k,vs2)
    def add_with_same_direction_subgroup(subgroup):
        (direction,sg)=subgroup
        sg2=map(lambda x:(x[0],x[1][1:]), sg)
        return (smul,[direction,(sadd,sg2)])
    def add_with_same_direction(group):
        (k,gs)=group
        gs2=sort_and_group_by_function(gs,lambda x: x[1][0])
        gs3=map(add_with_same_direction_subgroup,gs2)
        return (smul,[k,gs3])

    summand_groups = sort_and_group_by_function(entry[1],grp_key)
    summand_groups_direction = map(norm_summands,summand_groups)
    transformed_summands = map(add_with_same_direction,summand_groups_direction)
    return (entry[0],transformed_summands)

# if len(sys.argv) != 2:
#     print "Usage: %s <n>"%sys.argv[0]
#     print "Outputs the prime factorization of n."
#     sys.exit(1)

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# computations #

mTest = matrix(ZZ,[[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,2]])

mB_s = matrix(ZZ,[[4,1]])
mB_w = matrix(ZZ,[[0,0]])
mA = matrix(ZZ,[[-2,4],[4,0]])
(row_dim,col_dim)=mA.dimensions()
vZ = MX.mk_symbol_vector(col_dim,"x").transpose()

(mD,mP) = mA.jordan_form(QQbar,transformation=true)
mPi = mP.inverse()
evs=mD.eigenvalues()
evs_grouped=group_eigenvalues_by_abs(evs)
evs_indexset=eigenvalue_superset(evs_grouped)
abstract_fs=to_abstract_power_factors(mD)

print "is transformation matrix mP correct? ", mD == mPi * mA * mP
print "eigenvalues ", evs
print "eigenvalues sorted and grouped by absolute value ", evs_grouped
print "eigenvalue index set compact", evs_indexset
print "abstract factors of jordan matrix", abstract_fs

B=MX.mk_symbol_vector(2,"b")
P=MX.mk_symbol_matrix(2,2,"p")
D=MX.mk_symbol_matrix(2,2,"a")
Q=MX.mk_symbol_matrix(2,2,"q")

BPDQ=(B*P*D*Q).expand()           # .expand() is the same as .apply_map(expand)
# a matrix entry now has the form (apdq + apdq + apdq + ...), where each
# a,p,d,q corresponds to one entry of the original matrices.
#
# split into operators and operands
oBPDQ=map(lambda r: map (lambda c: formula_to_operands(c),r), MX.matrix_to_list(BPAQ))
# Now we have a list representation of our matrix where each entry is split
# into a tuple (operator,list of arguments).
# Here we want to replace the symbolic values of matrix A by some abstract
# representation of the Jordan matrix D to the power of some natural number
oBPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(A),MX.abstract_jordan_matrix_power(mD),oBPAQ)
# combine parts by same absolute eigenvalues and direction for every entry.
# an entry.
nBPdQ=MX.map_lmatrix(group_entry_summands_by_eigenvalue,oBPdQ)
# Entries now have the form (abs(a_0)(dir(a_0)pdq+dir(a_1)pdq+...)
# + abs(a_2)(dir(a_2)pdq+dir(a_3)pdq+...) + ...).
