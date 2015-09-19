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
import solve_extension as SE

#CCp=ComplexField(63)
reload(SE)

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

def positive_eigenspace_of(some_matrix):
    ess=some_matrix.eigenspaces_right()
    V=VectorSpace(QQbar,some_matrix.dimensions()[0])
    #pess=[]
    bases=[]
    for es in ess:
        if es[0] > 0:
            #pess.append(es)
            bases.extend(es[1].basis())
    pes=V.vector_space_span_of_basis(bases)
    return pes

# def positive_generalized_eigenspace_of(some_square_matrix):
#     jm = some_square_matrix.jordan_form(QQbar)
#     dim = some_square_matrix.dimensions()[0]
#     V = VectorSpace(QQbar,dim);
#     pvecs=[]
#     for i in range(dim):
#         if jm[i,i] > 0:
#             pvecs.append(jm.row(i))
#     pges=V.vector_space_span_of_basis(pvecs)
#     return pges

def big_and(*conds):
    # unused not working as intended.
    #
    # big_and is needed since all forces boolean evaluation
    # def all(iterable):
    # for element in iterable:
    #     if not element:
    #         return False
    # return True
    c = True
    for cond in conds:
        c = c and cond
        # print cond, bool(cond), c
    return c

#########################################################
# Lemma 6

def mk_abstract_cond_k_to_constraints(abs_cond_k, sorted_index_list, var_vector,only_positive_space,is_weak_part):
    # returns a index_z depending on abs_cond_k
    def condition_for_index(curr_idx,idx):
        if curr_idx > idx:
            if only_positive_space:
                #print "thecoeff:", abs_cond_k[curr_idx][QQbar(1)]
                coeff=matrix(map(lambda x:QQbar(x).radical_expression(),abs_cond_k[curr_idx][QQbar(1)]))
                lhs = (coeff*var_vector)[0,0]
                #print "coeff==:",coeff, "::", curr_idx, "::", idx, "::", lhs, "::", lhs == 0
                return [lhs == 0]
            else:
                coeffs=map(lambda vec:matrix(map(lambda x:QQbar(x).radical_expression(),vec)),
                    abs_cond_k[curr_idx].values())
                lhss = map(lambda coeff:(coeff*var_vector)[0,0],coeffs)
                return map(lambda lhs:lhs == 0,lhss)
        elif curr_idx == idx:
            if only_positive_space:
                #print "thecoeff:", abs_cond_k[curr_idx][QQbar(1)]
                coeff=matrix(map(lambda x:QQbar(x).radical_expression(),abs_cond_k[curr_idx][QQbar(1)])) #[0,0]
                lhs = (coeff*var_vector)[0,0]
                #print "coeff>:",coeff, "::", curr_idx, "::", idx, "::", lhs , "::", lhs > 0
                return [lhs > 0]
            else:
                return[]
        else:
            if only_positive_space:
                #return [True]
                return []
            else:
                return []
    def conditions_for_index(rev_idxs, idx):
        #print "index:", idx
        c = map(lambda cidx:condition_for_index(cidx,idx),rev_idxs)
        #print "c",idx,":", c , "==>" , big_and(*c)
        return list(itertools.chain(*c)) #big_and(*c)
    def conditions_for_indices(rev_idxs):
        idxs=list(rev_idxs)
        if is_weak_part: # hack to introduce None as zero index
            idxs.append(0)
        cs = zip(idxs,
            map(lambda idx:conditions_for_index(rev_idxs,idx),idxs)
            )
        return cs
    def subsdict(var_vector,num_vector):
        return dict(zip(var_vector.list(),num_vector.list()))
    def index_z(idx_cond_tuples,var_vector,num_vector):
            # partial index_z function needs to be associated to a k
            def handle_expression(d,exp):
                if isinstance(exp,bool):
                    return exp
                else:
                    return exp.substitute(d)
            d=subsdict(var_vector,num_vector)
            for (i,cs) in idx_cond_tuples:
                num_cs=map(lambda c: handle_expression(d,c),cs)
                # print num_cs, all(num_cs)
                if all(num_cs):
                    return i
            return None
    rev_idxs=list(reversed(sorted_index_list))
    idx_cond_tuples = conditions_for_indices(rev_idxs)
    # print "rev_idxs",list(rev_idxs)
    # print "idx_cond_tuples",idx_cond_tuples
    partial_index_z = functools.partial(index_z,idx_cond_tuples,var_vector)
    return (partial_index_z,idx_cond_tuples)

def mk_abstract_conds_to_constraints(abs_conds, sorted_index_list, var_vector,only_positive_space, is_weak_part):
    func_cond_tuple_list=map(lambda cond_k:
            mk_abstract_cond_k_to_constraints(cond_k,sorted_index_list,var_vector,only_positive_space, is_weak_part), abs_conds)
    return func_cond_tuple_list

def mk_index_z(s_abs_conds, w_abs_conds, sorted_index_list, var_vector):
    s_indices=filter(lambda x: x[0] != QQbar(0) and x[0] != 0, sorted_index_list)
    w_indices=sorted_index_list
    s_func_cond_tuple_list=mk_abstract_conds_to_constraints(s_abs_conds,s_indices,var_vector,True,False) # index_z uses only the positive eigenspace.
    w_func_cond_tuple_list=mk_abstract_conds_to_constraints(w_abs_conds,w_indices,var_vector,True,True) # weak part
    # print "wfunc:",w_func_cond_tuple_list
    index_z_func_list=map(lambda tup:tup[0],s_func_cond_tuple_list + w_func_cond_tuple_list)
    index_cond_tuples=map(lambda tup:tup[1],s_func_cond_tuple_list + w_func_cond_tuple_list)
    def index_z_k(index_z_list,num_vector_z, row_k):
        return index_z_list[k](num_vector_z)
    return (functools.partial(index_z_k,index_z_func_list),index_cond_tuples)

def mk_in_space_conditions(space,var_vector):
    basis_matrix = space.matrix().transpose().apply_map(lambda x:QQbar(x).radical_expression())
    vec_len,coeff_count = basis_matrix.dimensions()
    coeffs = MX.mk_symbol_vector(coeff_count,'c');
    #print "mk_in_space_condition:", coeff_count, coeffs, vec_len
    #print basis_matrix
    #for i in range(coeff_count):
    #    assume(coeffs[0][i],'rational')

    lhs1 = MX.linear_combination_of(coeffs,basis_matrix).list()
    lhs2 = var_vector.list()
    conds=map(lambda tup: tup[0] - tup[1] == 0,zip(lhs1,lhs2))
    return (conds,coeffs.list(),var_vector.list())

#########################################################
# Lemma 7

def max_index_cond_k(cond_tuples,k,var_vec,in_pos_eigenspace_conds):
    cond_k = cond_tuples[k]
    rest_conds = map(lambda cts:map(lambda ct: ct[1], cts),
        cond_tuples[0:k] + cond_tuples[k+1:])
    rest_conditions_combinations = map(lambda css: list(itertools.chain(*css)),
        SE.any_combination_of(rest_conds))
    vars=in_pos_eigenspace_conds[1]+in_pos_eigenspace_conds[2]
    for idx,conds in cond_k:
        cond_disjunct=map(lambda cs:cs+in_pos_eigenspace_conds[0]+conds,rest_conditions_combinations)
        # print idx, cond_disjunct, in_pos_eigenspace_conds[1]+in_pos_eigenspace_conds[2]
        solutions=SE.solve_ext(cond_disjunct,*vars)
        # print "solutions:", solutions
        if len(solutions) > 0:
            return (idx,solutions)
    return (None,[])

def max_indices_cond(cond_tuples,var_vec,in_pos_eigenspace_conds):
    result=[]
    for k in range(len(cond_tuples)):
        r=max_index_cond_k(cond_tuples,k,var_vec,in_pos_eigenspace_conds)
        #print "mx_idx_k",k,r
        #print "cond_t_k:",cond_tuples[k]
        if r[0] == None:
           # could not find an index for condition k
           return None
        result.append((r[0],r[1][0]))        # only take the first solutions if there are more
    return result

#########################################################
# Lemma 8

def complex_space_conditions(s_abs_conds,w_abs_conds,sorted_index_list,var_vec,index_cond_c_tuples,max_indices_cond_tuples,in_space_conds):
    s_index_cond_cn_tuples = mk_abstract_conds_to_constraints(s_abs_conds,sorted_index_list,var_vec,False,False)
    w_index_cond_cn_tuples = mk_abstract_conds_to_constraints(w_abs_conds,sorted_index_list,var_vec,False,True)
    # print index_cond_cn_tuples
    vars=in_space_conds[1]+in_space_conds[2]
    sc=in_space_conds[0]
    c_cond_dicts= map(lambda tup:dict(tup),index_cond_c_tuples)
    cn_cond_dicts = map(lambda tup:dict(tup[1]),s_index_cond_cn_tuples+w_index_cond_cn_tuples)
    #print "c-dicts", c_cond_dicts
    #print "cn-dicts", cn_cond_dicts
    conds=[]
    for k in range(len(s_abs_conds+w_abs_conds)):
        #print k
        max_idx_k=max_indices_cond_tuples[k][0]
        # c = max_indices_cond_tuples[k][1]
        c = c_cond_dicts[k][max_idx_k]
        cn = cn_cond_dicts[k][max_idx_k]
        # print vars
        #print c,"::",cn,"::",sc
        #print solve(cn+c+sc,vars)
        #conds.append(cn+c+sc)
        conds.append(cn)
    return (solve(list(itertools.chain(*conds)),vars,explicit_solutions=True),vars)

#########################################################
# Section 4.2 Looking for rational points in S_min

def collect_QQ_extends(matrix):
    def get_extensions (entry):
        nfe = entry.as_number_field_element()
        nf= nfe[2]
        #print nf.im_gens()
        return set(nf.im_gens())
        # #alternative to only get root expressions
        # op = entry.operator()
        # print entry
        # if op == None:
        #     return set()
        # elif op == operator.pow and abs(entry.operands()[1]) < 1:
        #     return {entry}
        # else:
        #     sets=map(get_extensions,entry.operands())
        #     return set.union(*sets)
    # exts = set.union(*map(get_extensions,matrix.list()))
    # return filter(lambda e: e != 1 and not e in QQ, list(exts))
    exts = set.union(*map(get_extensions,matrix.list()))
    return filter(lambda e: e != 1 and not e in QQ, list(exts))


def find_Q_min(S_min,space_exts):
    def solve_for_one_nonzero_variable(conditions,vars):
        conds=[]
        for var in vars:
            conds.append(conditions+[var != 0])
        #print conds
        solutions=SE.solve_ext(conds,*vars)
        return solutions
    def gen_vars(col_count,exts):
        vardict=dict()
        vars=[]
        for c in range(col_count):
            vardict[c]=dict()
            for e_id in range(len(exts)):
                v=var("v_c"+str(c)+"_e"+str(e_id))
                vardict[c][exts[e_id]]=v
                vars.append(v)
                assume(v,'rational')
        return vardict,vars
    def solution_to_coefficients(solution,vardict,vars):
        idict=dict()
        for eq in solution:
            for v in vars:
                if eq.operator() == operator.eq:
                    if eq.lhs() == v:
                        idict[v]=eq.rhs()
                    if eq.rhs() == v:
                        idict[v]=eq.lhs()
                if eq.operator() == operator.ne:
                    if (eq.lhs() == v and eq.rhs() == 0) or (eq.rhs() == v and eq.lhs() == 0):
                        idict[v] = SR(1)
        idict = dict(map(lambda x:(x[0],x[1].substitute(idict)),idict.items())) # maybe mor than one subtitution step is needed
        coeffs=[]
        for c in vardict.keys():
            coeff=0
            for ext in vardict[c].keys():
                v = vardict[c][ext]
                if not idict.has_key(v):
                    idict[v]=0
                coeff = coeff + idict[v]*ext.radical_expression()
            coeffs.append(coeff)
        # print "idict",idict
        return coeffs

    S_min_matrix = S_min.matrix().transpose()
    dims = S_min_matrix.dimensions()
    vecs = S_min_matrix.columns()
    exts = map(abs,[AA(1)]+space_exts) # it does not suffice to take the space extension of S_min
    # print exts
    conditions=[]
    vardict,vars=gen_vars(dims[1],exts)
    for r in range(dims[0]):
        #print "row", S_min_matrix.row(r)
        d=dict()
        for c in range(dims[1]):
            for e_id in range(len(exts)):
                num_part=QQbar(S_min_matrix[r,c])*exts[e_id]
                nf_gens=QQbar(num_part).as_number_field_element()[2].im_gens()
                # print "np:",vardict[c][exts[e_id]],num_part,nf_gens
                signf=1
                if QQbar(num_part) < 0:
                    signf = -1
                for gen in nf_gens:
                    #v=var("v_c"+str(c)+"_e"+str(e_id))
                    v=vardict[c][exts[e_id]]
                    k=abs(gen) # only use positive extensions as key
                    if d.has_key(k):
                        d[k].append(signf*v)
                    else:
                        d[k] = [signf*v]
            # print "d:",d
        for ext in d.keys():
            #print ext,ext != 1
            if ext != 1:
                conditions.append(sum(d[ext]) == 0)
    # print "basic conditions", conditions
    # print vardict
    # print vars
    solutions= solve_for_one_nonzero_variable(conditions,vars)
    # print solutions
    # reduce to real solutions not containing 0 != 0
    solutions= SE.solve_ext(solutions,vars)
    # print solutions
    forget() # forget that the variables are rational
    coeffs=map(lambda s: solution_to_coefficients(s,vardict,vars),solutions)
    # print "coeffs",coeffs
    vecs=map(lambda v:MX.linear_combination_of(vector(v),S_min_matrix),coeffs)
    # print vecs
    V=VectorSpace(QQ,S_min.degree())
    Q_min=V.span(vecs)
    return Q_min
    # #running solve a second time to circumvent a 0 != 0 clause in solutions
    # solutions2 = SE.solve_ext(solutions,lvars)
    # print solutions2
    # forget()
    # return (solutions2,lvars)
# if len(sys.argv) != 2:
#     print "Usage: %s <n>"%sys.argv[0]
#     print "Outputs the prime factorization of n."
#     sys.exit(1)

#########################################################
# Section 4.2 Reducing A to a A' of size d x d

def apply_reduction_on(cs_matrix,cw_matrix,alphas,alpha_lin):
    a_vec=vector(alphas)
    cs = map(
        lambda r:map(
            lambda c:var("Bs_"+str(r)+"_"+str(c)),
            range(len(alphas))),
        range(cs_matrix.dimensions()[0]))
    cw = map(
        lambda r:map(
            lambda c:var("Bw_"+str(r)+"_"+str(c)),
            range(len(alphas))),
        range(cw_matrix.dimensions()[0]))
    crmx=matrix(cs+cw)
    cvars=crmx.list()
    cmx=matrix(cs_matrix.rows() + cw_matrix.rows())
    lhs = cmx * alpha_lin
    rhs = crmx * a_vec
    conditions=map(lambda r:lhs[r] - rhs[r] == 0, range(crmx.dimensions()[0]))
    #print conditions
    sol_dict=solve(conditions,cvars,solution_dict=True)[0]
    #print sol_dict
    allvars=set.union(*map(lambda x:set(x.variables()),sol_dict.values()))
    fvars=allvars.difference(set(alphas))
    var_dict= dict(zip(fvars,[1]*len(fvars)) + zip(alphas,[1]*len(alphas)))
    nsol_dict= dict(map(lambda x:(x[0],x[1].substitute(var_dict)),sol_dict.items()))
    cs_n= matrix(cs).apply_map(lambda x:x.substitute(nsol_dict))
    cw_n= matrix(cw).apply_map(lambda x:x.substitute(nsol_dict))
    return (cs_n,cw_n)

def find_reduction_of_matrix(matrix,subspace):
    def gen_vars(d):
        alphas=[]
        betas=[]
        for i in range(d):
            alphas.append(var("a_"+str(i),latex_name="\\alpha_"+str(i)))
            betas.append(var("b_"+str(i),latex_name="\\beta_"+str(i)))
        return (alphas,betas)
    subspace_basis=subspace.matrix().transpose()
    dims=subspace_basis.dimensions()
    alphas,betas = gen_vars(dims[1]) # generate variables for each columns
    alpha_lin=MX.linear_combination_of(vector(alphas),subspace_basis)
    beta_lin=MX.linear_combination_of(vector(betas),subspace_basis)
    # print subspace_basis
    # print alphas,alpha_lin
    # print betas,beta_lin
    # print matrix*alpha_lin
    nbetas = (matrix * alpha_lin).list()
    # #deprecated code
    # vec_lhs = matrix * alpha_lin
    # vec_rhs = beta_lin
    # conditions=[]
    # for r in range(dims[0]):
    #     conditions.append(vec_lhs[r] - vec_rhs[r] == 0)
    # print conditions
    # sol_dict=solve(conditions,betas,solution_dict=True)[0]
    # nbetas=map(lambda x:x.substitute(sol_dict),betas)
    red_mx_s=MX.mk_symbol_matrix(dims[1],dims[1],"A") # reduced symbolic matrix
    red_mx_vars=red_mx_s.list()
    lhs = red_mx_s * vector(alphas)
    rhs = nbetas
    conditions=map(lambda i: lhs[i] - rhs[i] == 0,range(dims[1]))
    # print conditions
    sol_dict=solve(conditions,red_mx_vars,solution_dict=True)[0]
    # print sol_dict
    allvars=set.union(*map(lambda x:set(x.variables()),sol_dict.values()))
    fvars=allvars.difference(set(alphas))
    var_dict= dict(zip(fvars,[1]*len(fvars)) + zip(alphas,[1]*len(alphas)))
    nsol_dict= dict(map(lambda x:(x[0],x[1].substitute(var_dict)),sol_dict.items()))
    # print nsol_dict
    red_mx_n= red_mx_s.apply_map(lambda x:x.substitute(nsol_dict))
    return (red_mx_n,alphas,alpha_lin)

#########################################################
# zero vector termination check

def terminates_on_zero(B_s,B_w):
    zv = zero_vector(B_s.dimensions()[1])
    s_conds=map(lambda x:x>0,(B_s * zv).list())
    w_conds=map(lambda x:x>=0,(B_w * zv).list())
    if all(s_conds+w_conds):
        return False
    else:
        return True

#########################################################
# main termination check function

def clean_up(vs):
    forget()
    reset(vs)

def termination_check(matrix_A,matrix_B_s,matrix_B_w):
    mA   = matrix_A
    mB_s = matrix_B_s
    mB_w = matrix_B_w

    zvec = MX.mk_symbol_vector(mA.dimensions()[0],"z").transpose()
    #########################################################
    # 1. compute JNF
    (mD,mP) = mA.jordan_form(QQbar,transformation=true)
    mPi = mP.inverse()

    #########################################################
    # 2. find factors porresponding to entries in A in BPDQ
    sB_dims=mB_s.dimensions()
    wB_dims=mB_w.dimensions()
    A_dims=mA.dimensions()
    sB=MX.mk_symbol_matrix(sB_dims[0],sB_dims[1],"bs")
    wB=MX.mk_symbol_matrix(wB_dims[0],wB_dims[1],"bw")
    P=MX.mk_symbol_matrix(A_dims[0],A_dims[1],"p")
    D=MX.mk_symbol_matrix(A_dims[0],A_dims[1],"a")  # entries of this matrix must be sorted first when expanding
                                    # to make the algorithm work. Hence it is called "a"
    Q=MX.mk_symbol_matrix(A_dims[0],A_dims[1],"q")

    sBPDQ=(sB*P*D*Q).expand()           # .expand() is the same as .apply_map(expand)
    wBPDQ=(wB*P*D*Q).expand()
    # a matrix entry now has the form (apdq + apdq + apdq + ...), where each
    # a,p,d,q corresponds to one entry of the original matrices.
    #
    # split into operators and operands
    soBPDQ=map(lambda r: map (lambda c: formula_to_operands(c),r), MX.matrix_to_list(sBPDQ))
    woBPDQ=map(lambda r: map (lambda c: formula_to_operands(c),r), MX.matrix_to_list(wBPDQ))
    # Now we have a list representation of our matrix where each entry is split
    # into a tuple (operator,list of arguments).
    # Here we want to replace the symbolic values of matrix A by some abstract
    # representation of the Jordan matrix D to the power of some natural number
    soBPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(D),MX.abstract_jordan_matrix_power(mD),soBPDQ)
    woBPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(D),MX.abstract_jordan_matrix_power(mD),woBPDQ)
    # combine parts by same absolute eigenvalues and direction for every entry.
    # an entry.
    snBPdQ=MX.map_lmatrix(group_entry_summands_by_eigenvalue,soBPdQ)
    wnBPdQ=MX.map_lmatrix(group_entry_summands_by_eigenvalue,woBPdQ)
    # Entries now have the form (abs(a_0)(dir(a_0)pdq+dir(a_1)pdq+...)
    # + abs(a_2)(dir(a_2)pdq+dir(a_3)pdq+...) + ...).
    # Next the variables b p q are replaced by their values.
    snbPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(sB),MX.matrix_to_list(mB_s),snBPdQ)
    snbpdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(P),MX.matrix_to_list(mP),snbPdQ)
    snbpdq=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(Q),MX.matrix_to_list(mPi),snbpdQ)

    wnbPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(wB),MX.matrix_to_list(mB_w),wnBPdQ)
    wnbpdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(P),MX.matrix_to_list(mP),wnbPdQ)
    wnbpdq=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(Q),MX.matrix_to_list(mPi),wnbpdQ)

    #########################################################
    # 3. build the index set and abstract conditions
    ind=sorted(list(set.union(abs_ev_index_set_from_abstract_lmatrix(snbpdq),
        abs_ev_index_set_from_abstract_lmatrix(wnbpdq))))
    s_abs_conds = mk_abstract_conds(snbpdq)
    w_abs_conds = mk_abstract_conds(wnbpdq)

    #########################################################
    # 4. build index_z function  and conditions for each index and constraint
    index_z_k,index_cond_c_tuples = mk_index_z(s_abs_conds,w_abs_conds,ind,zvec)

    #########################################################
    # 5. build positive eigenspace and constraints for vectors inside of it
    pos_eigenspace = positive_eigenspace_of(mA)
    in_space_conds = mk_in_space_conditions(pos_eigenspace,zvec)

    #########################################################
    # 6. collect all variables and coefficients used
    c_vars=in_space_conds[1] # coefficients
    v_vars=in_space_conds[2] # variables (from zvec)
    allvars=in_space_conds[1]+in_space_conds[2]

    #########################################################
    # 7. compute the maxial satisfying index for each of the k constraints
    max_indices = max_indices_cond(index_cond_c_tuples,zvec,in_space_conds)

    if max_indices == None:
        # when no index function can be found (= no nonterminating
        # susbspace is found = dimension of S_min is zero)
        print "case 0: terminating"
        return "terminating"

    #########################################################
    # 8. compute S_min
    S_min_conds=complex_space_conditions(s_abs_conds,w_abs_conds,ind,zvec,index_cond_c_tuples,max_indices,in_space_conds)
    S_min = SE.solution_to_space(S_min_conds[0][0],c_vars,v_vars)

    #########################################################
    # 9. compute Q_min and R_min
    algebraic_base_extends = collect_QQ_extends(mD)
    Q_min=find_Q_min(S_min,algebraic_base_extends)
    R_min=VectorSpace(SR,Q_min.degree()).subspace_with_basis(Q_min.basis())

    #########################################################
    # 10. decide termination
    if S_min.dimension() == Q_min.dimension():
        print "case 1: non-terminating"
        clean_up(allvars)
        return "non-terminating"
    if Q_min.dimension() == 0:
        #########################################################
        # 10.2 test whether zero vector is non-terminating
        if terminates_on_zero(mB_s,mB_w):
            print "case 2: terminating"
            clean_up(allvars)
            return "terminating"
        else:
            return "case 2: non-terminating"
            clean_up(allvars)
            return "non-terminating"
    if 0 < Q_min.dimension() < S_min.dimension():
        #########################################################
        # 10.3 run termination_check onr educed program
        print "case 3: reduce"
        rA,valphas,lin_alpha=find_reduction_of_matrix(mA,Q_min)
        rB_s,rB_w=apply_reduction_on(mB_s, mB_w, valphas,lin_alpha)
        clean_up(allvars)
        termination_check(rA,rB_s,rB_w)
#########################################################
# examples




# (row_dim,col_dim)=mA.dimensions()
# vZ = MX.mk_symbol_vector(col_dim,"x").transpose()

# (mD,mP) = mA.jordan_form(QQbar,transformation=true)
# mPi = mP.inverse()
# # evs=mD.eigenvalues()
# # evs_grouped=group_eigenvalues_by_abs(evs)
# # evs_indexset=eigenvalue_superset(evs_grouped)
# # abstract_fs=to_abstract_power_factors(mD)
#
# # print "is transformation matrix mP correct? ", mD == mPi * mA * mP
# # print "eigenvalues ", evs
# # print "eigenvalues sorted and grouped by absolute value ", evs_grouped
# # print "eigenvalue index set compact", evs_indexset
# # print "abstract factors of jordan matrix", abstract_fs
#
# sB_dims=mB_s.dimensions()
# wB_dims=mB_w.dimensions()
# A_dims=mA.dimensions()
# sB=MX.mk_symbol_matrix(sB_dims[0],sB_dims[1],"bs")
# wB=MX.mk_symbol_matrix(wB_dims[0],wB_dims[1],"bw")
# P=MX.mk_symbol_matrix(A_dims[0],A_dims[1],"p")
# D=MX.mk_symbol_matrix(A_dims[0],A_dims[1],"a")  # entries of this matrix must be sorted first when expanding
#                                 # to make the algorithm work. Hence it is called "a"
# Q=MX.mk_symbol_matrix(A_dims[0],A_dims[1],"q")
#
# sBPDQ=(sB*P*D*Q).expand()           # .expand() is the same as .apply_map(expand)
# wBPDQ=(wB*P*D*Q).expand()
# # a matrix entry now has the form (apdq + apdq + apdq + ...), where each
# # a,p,d,q corresponds to one entry of the original matrices.
# #
# # split into operators and operands
# soBPDQ=map(lambda r: map (lambda c: formula_to_operands(c),r), MX.matrix_to_list(sBPDQ))
# woBPDQ=map(lambda r: map (lambda c: formula_to_operands(c),r), MX.matrix_to_list(wBPDQ))
# # Now we have a list representation of our matrix where each entry is split
# # into a tuple (operator,list of arguments).
# # Here we want to replace the symbolic values of matrix A by some abstract
# # representation of the Jordan matrix D to the power of some natural number
# soBPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(D),MX.abstract_jordan_matrix_power(mD),soBPDQ)
# woBPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(D),MX.abstract_jordan_matrix_power(mD),woBPDQ)
# # combine parts by same absolute eigenvalues and direction for every entry.
# # an entry.
# snBPdQ=MX.map_lmatrix(group_entry_summands_by_eigenvalue,soBPdQ)
# wnBPdQ=MX.map_lmatrix(group_entry_summands_by_eigenvalue,woBPdQ)
# # Entries now have the form (abs(a_0)(dir(a_0)pdq+dir(a_1)pdq+...)
# # + abs(a_2)(dir(a_2)pdq+dir(a_3)pdq+...) + ...).
# # Next the variables b p q are replaced by their values.
# snbPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(sB),MX.matrix_to_list(mB_s),snBPdQ)
# snbpdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(P),MX.matrix_to_list(mP),snbPdQ)
# snbpdq=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(Q),MX.matrix_to_list(mPi),snbpdQ)
#
# wnbPdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(wB),MX.matrix_to_list(mB_w),wnBPdQ)
# wnbpdQ=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(P),MX.matrix_to_list(mP),wnbPdQ)
# wnbpdq=MX.replace_symbols_in_lmatrix(MX.matrix_to_list(Q),MX.matrix_to_list(mPi),wnbpdQ)
#
# # At this point we have somehow the representation for Cond_k for all k.
# # we transform it to a more concrete representation.
#
# # build eigenvalue index set Ind
# ind=sorted(list(set.union(abs_ev_index_set_from_abstract_lmatrix(snbpdq),
#     abs_ev_index_set_from_abstract_lmatrix(wnbpdq))))
# s_abs_conds = mk_abstract_conds(snbpdq)
# w_abs_conds = mk_abstract_conds(wnbpdq)
# zvec = MX.mk_symbol_matrix(2,1,"z")
# #cond_0=mk_abstract_cond_k_constraints_S_plus(abs_conds[0],ind,zvec)
# index_z_k,index_cond_c_tuples = mk_index_z(s_abs_conds,w_abs_conds,ind,zvec)
# pos_eigenspace = positive_eigenspace_of(mA)
# in_space_conds = mk_in_space_conditions(pos_eigenspace,zvec)
# c_vars=in_space_conds[1]
# v_vars=in_space_conds[2]
# allvars=in_space_conds[1]+in_space_conds[2]
# max_indices = max_indices_cond(index_cond_c_tuples,zvec,in_space_conds)
# S_min_conds=complex_space_conditions(s_abs_conds,w_abs_conds,ind,zvec,index_cond_c_tuples,max_indices,in_space_conds)
# S_min = SE.solution_to_space(S_min_conds[0][0],c_vars,v_vars)
# #   intersecting S_min with VectorSpace(QQ,n) does not work with sage math
# # methods since the ambient space is not the same.
# #   All space extensions are computed, because it does not suffice to only
# # only use space extensions from S_min
# algebraic_base_extends = collect_QQ_extends(mD)
# Q_min=find_Q_min(S_min,algebraic_base_extends)
# R_min=VectorSpace(SR,Q_min.degree()).subspace_with_basis(Q_min.basis())
#

#
# rA,valphas,lin_alpha=find_reduction_of_matrix(mA,Q_min)
# rB_s,rB_w=apply_reduction_on(mB_s, mB_w, valphas,lin_alpha)
#
#
# print "done"
#
# # testing the index function
# # a= cond[0][cond[0].keys()[2]][QQbar(1)]
# # cond_0[0](matrix([[-SR(a[1])],[SR(a[0])]]))
