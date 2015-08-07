# -*- coding: utf-8 -*-

##!/usr/bin/env sage -python

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# imports #

import sys

from itertools import groupby
from functools import partial

from sage.all import *

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# functions #

def mk_symbol_vector(dim,symbol):
    return matrix(1,dim, lambda i,j: var(
        symbol+"_"+str(i),
        latex_name=symbol+"_{"+str(i)+"}"))

def mk_symbol_matrix(rdim,cdim,symbol):
    return matrix(rdim,cdim, lambda i,j: var(
        symbol+"_"+str(i)+"_"+str(j),
        latex_name=symbol+"_{"+str(i)+","+str(j)+"}"))

def matrix_to_list(m):
    return map(lambda r:r.list(), m.rows())

def formula_to_operands(formula):
    fe=formula.expand()
    return (fe.operator(),map(lambda m:(m.operator(),m.operands()), fe.operands()))

def number_direction(num):
    return (num/abs(num))


def sort_and_group_values_by_abs(vals):
    groups = []
    uniquekeys = []
    data = sorted(vals, key=abs)
    for k, g in groupby(data, abs):
        # Store group iterator as a list
        groups.append(map(number_direction,list(g)))
        uniquekeys.append(k)
    return zip(uniquekeys,groups)


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

def to_jordan_blocks(jordan_matrix):
    (vdivs, hdivs) = jordan_matrix.subdivisions()
    block_count = len(vdivs)+1
    jbs=[]
    for d in range(0,block_count):
        jbs.append(jordan_matrix.subdivision(d,d))
    return jbs

def find_jordan_block_dim_from_eigenvalue(jbs, ev_tuple):
    dim=0
    ev=ev_tuple[0]
    for b in jbs:
        d = b.dimensions()[0]
        if ev == abs(b[0,0]) and d > dim:
            dim = d
    return dim

def to_abstract_power_factors(jordan_matrix):
    def handle_ev(abs_ds_tuple, max_block_size):
        (absval,dirs) = abs_ds_tuple
        fs=[]
        for i in range(0,max_block_size):
            fs.extend(map(lambda d: (absval,d,i), dirs))
        return fs

    evs = eigenvalue_superset(
        sort_and_group_values_by_abs(
        jordan_matrix.eigenvalues()))
    jbs = to_jordan_blocks(jordan_matrix)
    abstract_factors = []
    for ev in evs:
        size = find_jordan_block_dim_from_eigenvalue(jbs,ev)
        abstract_factors.extend(handle_ev(ev,size))
    return abstract_factors


def replace_symbol_matrix_entries(sym_mx,val_mx,abstract_symbol_matrix):
    # Wrapping a Symbolic Ring (SR) around potentially Algebric Numbers (QQbar)
    # is posssible, with loss of exactness if a transformation from SR back to
    # QQbar is needed. See:
    # https://groups.google.com/forum/#!topic/sage-support/Kfzd07Y1Q_s
    # Ignoring this problem we could write the following:
    #
    #   d=dict(zip(sym_mx.list(),map(SR,val_mx.list())))
    #   return expr.subs(d)
    #
    # But we want the substitutions to stay in the algebric numbers. Hence
    # we use a more complicated way to substitute.
    def replace(d,entry):
        new_entry = d.get(repr(entry))
        if new_entry is None:
            return entry
        else:
            return new_entry

    def walk_lists(d,lst):
        rec = partial(walk_lists,d)
        if isinstance(lst,list):    # if it is a list
            return map(rec,lst)
        elif isinstance(lst,tuple):  # if it is a tuple
            return (lst[0],map(rec,lst[1]))
        elif isinstance(lst,Expression): # an element
            return replace(d,lst)
        else:
            return lst
    d=dict(zip(map(repr,sym_mx.list()),map(SR,val_mx.list())))
    return walk_lists(d,abstract_symbol_matrix)



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
vZ = mk_symbol_vector(col_dim,"x").transpose()

(mD,mP) = mA.jordan_form(QQbar,transformation=true)
mPi = mP.inverse()
evs=mD.eigenvalues()
evs_grouped=sort_and_group_values_by_abs(evs)
evs_indexset=eigenvalue_superset(evs_grouped)
abstract_fs=to_abstract_power_factors(mD)

print "is transformation matrix mP correct? ", mD == mPi * mA * mP
print "eigenvalues ", evs
print "eigenvalues sorted and grouped by absolute value ", evs_grouped
print "eigenvalue index set compact", evs_indexset
print "abstract factors of jordan matrix", abstract_fs

B=mk_symbol_vector(2,"b")
P=mk_symbol_matrix(2,2,"p")
A=mk_symbol_matrix(2,2,"a")
Q=mk_symbol_matrix(2,2,"q")

BPAQ=(B*P*A*Q).expand()           # .expand() is the same as .apply_map(expand)
# splt into operators and operands
oBPAQ=map(lambda r: map (lambda c: formula_to_operands(c),r), matrix_to_list(BPAQ))
# insert vales for A matrix
oBPaQ=replace_symbol_matrix_entries(A,mD,oBPAQ)
# combine parts by same absolute eigenvalues and direction
