# -*- coding: utf-8 -*-

##!/usr/bin/env sage -python

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# imports #

import sys

import itertools
import functools

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
    for k,v in itertools.groupby(sorted_list, key_func):
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
        group_eigenvalues_by_abs(
        jordan_matrix.eigenvalues()))
    jbs = MX.to_jordan_blocks(jordan_matrix)
    abstract_factors = []
    for ev in evs:
        size = find_jordan_block_dim_from_eigenvalue(jbs,ev)
        abstract_factors.extend(handle_ev(ev,size))
    return abstract_factors



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
        # print "#"*30
        # print "k:=",k
        # print "gs3:=",gs3
        return (smul,[k,(sadd,gs3)])

    summand_groups = sort_and_group_by_function(entry[1],grp_key)
    summand_groups_direction = map(norm_summands,summand_groups)
    transformed_summands = map(add_with_same_direction,summand_groups_direction)
    return (entry[0],transformed_summands)

def abs_ev_index_set_from_abstract_lmatrix(lmatrix):
    def set_from_entry(entry):
        (op,vs) = entry
        evs = map(lambda v:v[1][0],vs)
        return set(evs)
    ev_sets = MX.map_lmatrix(set_from_entry,lmatrix)
    return set.union(*map(lambda s:set.union(*s),ev_sets))

def mk_abstract_cond_k(abstract_program_lmatrix,k):
    def directions_of_ev_part(ev_part):
        dirs = set()
        for summand in ev_part:
            dirs.add(summand[1][0])
        return dirs
    def get_direction_constant_factor(ev_part,dir):
        factor=0
        for summand in ev_part:
            if summand[1][0] == dir:
                addition = summand[1][1][0]
                factor_parts = map(lambda p: p[0](*p[1]),summand[1][1][1]) # multiply b p q values
                factor = addition(*factor_parts)
        return factor
    def merge_ev_parts(ev_parts):
        dirs = set.union(*map(directions_of_ev_part,ev_parts))
        dirs.add((QQbar(1),ZZ(0))) # do not drop power here
        factor_dict={}
        for dir in dirs:
            factor_vec = map(lambda p: get_direction_constant_factor(p,dir),ev_parts)
            # factor_dict[dir]=factor_vec # power not dropped for key
            factor_dict[dir[0]]=factor_vec # power is dropped for key since it is already encoded in eigenvalue tuple
        return factor_dict
    def get_ev_part_for_entry(entry, ev):
        summands=entry[1]
        ev_part=[]
        for s in summands:
            if s[1][0] == ev:
                ev_part=s[1][1][1] # the summands for each direction corresponding to ev
        return ev_part
    def mk_cond_part_for_ev(row, ev):
        ev_parts = map(lambda e:get_ev_part_for_entry(e,ev),row)
        ev_dict = merge_ev_parts(ev_parts)
        return ev_dict

    index_set=abs_ev_index_set_from_abstract_lmatrix(abstract_program_lmatrix)
    kth_row = abstract_program_lmatrix[k]
    cond_k_dict={}
    for ev in index_set:
        cond_k_dict[ev]=mk_cond_part_for_ev(kth_row, ev)
    return cond_k_dict

def mk_abstract_conds(abstract_program_lmatrix):
    cond_ks=[]
    for k in range(0,len(abstract_program_lmatrix)):
        cond_ks.append(mk_abstract_cond_k(abstract_program_lmatrix,k))
    return cond_ks

def reduce_abstract_cond_k_to_S_plus(cond_k):
    evs=abs_cond_k.keys()
    cond_k_sp={}
    for ev in evs:
        ev_part=cond_k[ev]
        positive_dir_factor=ev_part[(QQbar(1))]
        cond_k_sp[ev]={QQbar(1) : positive_dir_factor}
    return cond_k_sp

def big_and(*conds):
    # big_and is needed since all forces boolean evaluation
    # def all(iterable):
    # for element in iterable:
    #     if not element:
    #         return False
    # return True
    c = True
    for cond in conds:
        c = c and cond
    return c


def mk_abstract_cond_k_constraints_S_plus(abs_cond_k, sorted_index_list, var_vector):
    # returns a index_z depending on abs_cond_k
    def condition_for_index(curr_idx,idx):
        if curr_idx > idx:
            coeff=matrix(map(SR,abs_cond_k[idx][QQbar(1)]))
            lhs = (coeff*var_vector)[0,0]
            # print "coeff==:",lhs, lhs == 0
            return lhs == 0
        elif curr_idx == idx:
            coeff=matrix(map(SR,abs_cond_k[idx][QQbar(1)]))[0,0]
            lhs = (coeff*var_vector)[0,0]
            # print "coeff>:",lhs , lhs == 0
            return lhs > 0
        else:
            return True
    def conditions_for_index(rev_idxs, idx):
        c = map(lambda cidx:condition_for_index(cidx,idx),rev_idxs)
        print "c",idx,":", c , "==>" , big_and(*c)
        return big_and(*c)
    def conditions_for_indices(rev_idxs):
        cs = zip(rev_idxs,
            map(lambda idx:conditions_for_index(rev_idxs,idx),rev_idxs)
            )
        return cs
    def subsdict(var_vector,num_vector):
        return dict(zip(var_vector.list(),num_vector.list()))
    def index_z(idx_cond_tuples,var_vector,num_vector):
            d=subsdict(var_vector,num_vector)
            for (i,c) in idx_cond_tuples:
                num_c=c.substitute(d)
                print num_c
                if num_c:
                    return i
            return None
    rev_idxs=list(reversed(sorted_index_list))
    idx_cond_tuples = conditions_for_indices(rev_idxs)
    print "rev_idxs",list(rev_idxs)
    print "idx_cond_tuples",idx_cond_tuples
    partial_index_z = partial(index_z,idx_cond_tuples,var_vector)
    return (partial_index_z,idx_cond_tuples)

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
# mA = matrix(ZZ,[[-1,0],[0,1]])
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

B=MX.mk_symbol_matrix(1,2,"b")
P=MX.mk_symbol_matrix(2,2,"p")
D=MX.mk_symbol_matrix(2,2,"a")  # entries of this matrix must be sorted first when expanding
                                # to make the algorithm work. Hence it is called "a"
Q=MX.mk_symbol_matrix(2,2,"q")

BPDQ=(B*P*D*Q).expand()           # .expand() is the same as .apply_map(expand)
# a matrix entry now has the form (apdq + apdq + apdq + ...), where each
# a,p,d,q corresponds to one entry of the original matrices.
#
# split into operators and operands
oBPDQ=map(lambda r: map (lambda c: formula_to_operands(c),r), MX.matrix_to_list(BPDQ))
# Now we have a list representation of our matrix where each entry is split
# into a tuple (operator,list of arguments).
# Here we want to replace the symbolic values of matrix A by some abstract
# representation of the Jordan matrix D to the power of some natural number
oBPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(D),MX.abstract_jordan_matrix_power(mD),oBPDQ)
# combine parts by same absolute eigenvalues and direction for every entry.
# an entry.
nBPdQ=MX.map_lmatrix(group_entry_summands_by_eigenvalue,oBPdQ)
# Entries now have the form (abs(a_0)(dir(a_0)pdq+dir(a_1)pdq+...)
# + abs(a_2)(dir(a_2)pdq+dir(a_3)pdq+...) + ...).
# Next the variables b p q are replaced by their values.
nbPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(B),MX.matrix_to_list(mB_s),nBPdQ)
nbpdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(P),MX.matrix_to_list(mP),nbPdQ)
nbpdq=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(Q),MX.matrix_to_list(mPi),nbpdQ)
# At this point we have somehow the representation for Cond_k for all k.
# we transform it to a more concrete representation.

# build eigenvalue index set Ind
ind=abs_ev_index_set_from_abstract_lmatrix(nbpdq)
cond=mk_abstract_conds(nbpdq)
zvec=MX.mk_symbol_matrix(2,1,"z")
cond_0=mk_abstract_cond_k_constraints_S_plus(cond[0],sorted(list(ind)),zvec)

# testing the index function
# a= cond[0][cond[0].keys()[2]][QQbar(1)]
# cond_0[0](matrix([[-SR(a[1])],[SR(a[0])]]))
