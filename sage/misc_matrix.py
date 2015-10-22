
import itertools
import functools
import inspect

from sage.all import *


def mk_symbol_vector(dim,symbol):
    return matrix(1,dim, lambda i,j: var(
        symbol+"_"+str(j),
        latex_name=symbol+"_{"+str(j)+"}"))

def mk_symbol_matrix(rdim,cdim,symbol):
    return matrix(rdim,cdim, lambda i,j: var(
        symbol+"_"+str(i)+"_"+str(j),
        latex_name=symbol+"_{"+str(i)+","+str(j)+"}"))

def matrix_to_list(m):
    return map(lambda r:r.list(), m.rows())

def map_lmatrix(func,lmatrix):
    return map(lambda row: map(lambda entry: func(entry), row), lmatrix)


def lmatrix_from_diagonal_lblocks(lblocks,zero_elem):
    def combine_blocks(block1, block2):
        # print "b1:",block1
        # print "b2:",block2
        rows1=len(block1)
        cols1=len(block1[0])
        rows2=len(block2)
        cols2=len(block2[0])
        lmatrix=[]
        for i in range(0,rows1+rows2):
            row=[]
            for j in range(0,cols1+cols2):
                # print i,j
                if i < rows1 and j < cols1:
                    row.append(block1[i][j])
                elif i >= rows1 and j >= cols1:
                    row.append(block2[i-rows1][j-cols1])
                else:
                    row.append(zero_elem)
            lmatrix.append(row)
        return lmatrix
    # print lblocks
    mx=lblocks[0]
    for i in range(1,len(lblocks)):
        mx=combine_blocks(mx,lblocks[i])
    return mx

def to_jordan_blocks(jordan_matrix):
    (vdivs, hdivs) = jordan_matrix.subdivisions()
    block_count = len(vdivs)+1
    jbs=[]
    for d in range(0,block_count):
        jbs.append(jordan_matrix.subdivision(d,d))
    return jbs

def abstract_jordan_matrix_power(jordan_matrix):
    blocks = to_jordan_blocks(jordan_matrix)
    def block_power(block):
        dims = block.dimensions() # (rows,cols)
        ev = block[0][0]
        ablock=matrix_to_list(block)
        for i in range(0,dims[0]):
            for j in range(0,dims[1]):
                if j-i >= 0:
                    ablock[i][j]=(ev,j-i)
                else:
                    ablock[i][j]=(0,0)
        return ablock
    return lmatrix_from_diagonal_lblocks(map(block_power,blocks),(0,0))

def replace_symbols_in_lmatrix(lmx_sym,lmx_val,lmatrix):
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
        rec = functools.partial(walk_lists,d)
        if isinstance(lst,list):    # if it is a list: matrix structure or parameters
            return map(rec,lst)
        elif isinstance(lst,tuple) and inspect.isfunction(lst[0]):  # if it is a tuple: function and pararmeter
            return (lst[0],map(rec,lst[1]))
        elif isinstance(lst,Expression): # an element: variable
            return replace(d,lst)
        else: # cannot replace
            return lst
    lst_sym=list(itertools.chain(*lmx_sym))
    lst_val=list(itertools.chain(*lmx_val))
    d=dict(zip(map(repr,lst_sym),lst_val))
    #print d
    return walk_lists(d,lmatrix)

def linear_combination_of(coefficient_vec,matrix):
    coeffs=coefficient_vec.list()
    vecs=matrix.columns()
    lc=0
    for c,v in zip(coeffs,vecs):
        lc = lc + c * v
    return lc

def solve_system_of_linear_equalities(mx,vec):
    symbol_vec=mk_symbol_vector(mx.dimensions()[1], "v").transpose()
    vars = symbol_vec.list()
    # print "mx",mx
    # print "symbol_vec",symbol_vec
    lhs = mx * symbol_vec
    rhs = vec
    # print "lhs",lhs
    # print "rhs",rhs
    eqs = map(lambda e:e[0]-e[1]==0, zip(lhs.list(),rhs.list()))
    # print eqs
    sols = solve(eqs,vars,solution_dict=True)
    if len(sols) == 0:
        return None
    else:
        sol=sols[0]
        fvars=set.union(*map(lambda s: set(s.variables()),sol.values())).difference(set(vars))
        rdict= dict(zip(list(fvars),[1]*len(list(fvars))))
        # print rdict
        # print isol
        isol=dict(map(lambda s:(s[0],s[1].substitute(rdict)),sol.items()))
        val_vec=symbol_vec.substitute(isol)
        # print val_vec
        return val_vec.change_ring(vec.base_ring())

def generalized_eigenvectors_for(mx,ev,evec):
    mxI=mx - ev * identity_matrix(mx.dimensions()[0])
    gen_evecs=[]
    rem_vec=matrix([evec]).transpose()
    while rem_vec != None:
        gen_evecs.append(rem_vec)
        rem_vec = solve_system_of_linear_equalities(mxI,rem_vec)
    return gen_evecs
