
import itertools
import operator
import sage.all as S

def solve_ext(list_of_conditions,*args,**kwds):
    # takes multiple conditions and gives them to solve.
    # Each condition is an input for solve, ususally a conjunct of
    # equations. The list of conditions is interpreted as a disjunct of conditions.
    solutions = []
    for cond in list_of_conditions:
        sol=S.solve(cond,*args,**kwds)
        # if sol != []:
        #     print "cons:", cond
        #     print "sol :", sol
        solutions.extend(sol)
    return solutions

def solve_single(list_of_conditions,vars,**kwds):
    sol = []
    for v in vars:
        sol +=  S.solve(list_of_conditions,vars,**kwds)
    return sol

def any_combination_of(list_of_element_lists):
    if list_of_element_lists == []:
        return [[]]
    else:
        head=list_of_element_lists[0]
        tail=list_of_element_lists[1:]
        #print head, tail
        comb_lists=any_combination_of(tail)
        new_comb_lists=[]
        for e in head:
            lsts= map(lambda l:[e]+l,comb_lists)
            new_comb_lists.extend(lsts)
        return new_comb_lists

def find_instance_for_solution_equations(equations):
    # assuming the equations are consistent and have a
    # single symbol at the lefthandside or righthandside.
    # every stand alone symbol is assigned to a quintuple (gt,gte,eq,lte,lt)
    # in which every entry represents a bound on the symbol
    def eq_to_tuple(lhs,rhs):
        if lhs.is_symbol() and rhs.is_symbol():
            return [(lhs,(None,None,rhs,None,None)),(rhs,(None,None,lhs,None,None))]
        elif lhs.is_symbol():
            return [(lhs,(None,None,rhs,None,None))]
        else: # rhs has to be a symbol by assumption
            return [(rhs,(None,None,lhs,None,None))]
    def gt_to_tuple(lhs,rhs):
        if lhs.is_symbol() and rhs.is_symbol():
            return [(lhs,(rhs,None,None,None,None)),(rhs,(None,None,None,None,lhs))]
        elif lhs.is_symbol():
            return [(lhs,(rhs,None,None,None,None))]
        else:
            return [(rhs,(None,None,None,None,lhs))]
    def gte_to_tuple(lhs,rhs):
        if lhs.is_symbol() and rhs.is_symbol():
            return [(lhs,(None,rhs,None,None,None)),(rhs,(None,None,None,lhs,None))]
        elif lhs.is_symbol():
            return [(lhs,(None,rhs,None,None,None))]
        else:
            return [(rhs,(None,None,None,lhs,None))]
    def equation_to_dict_tuple(equation):
        tuples = []
        if equation.operator() == operator.eq:
            tuples = eq_to_tuple(equation.lhs(),equation.rhs())
        elif equation.operator() == operator.gt:
            tuples = gt_to_tuple(equation.lhs(),equation.rhs())
        elif equation.operator() == operator.lt:
            tuples = gt_to_tuple(equation.rhs(),equation.lhs())
        elif equation.operator() == operator.gte:
            tuples = gte_to_tuple(equation.lhs(),equation.rhs())
        elif equation.operator() == operator.lte:
            tuples = gte_to_tuple(equation.rhs(),equation.lhs())
        return tuples
    def update_tuples(d,ut):
        # dictionary and update tuple
        if not d.has_key(ut[0]):
            d[ut[0]]=list(ut[1])
        else: # has a tuple with same key as ut
            tup=d[ut[0]]
            otup=ut[1]
            if tup[0] == None or tup[0] < otup[0]:
                tup[0]=otup[0]
            if tup[1] == None or tup[1] < otup[1]:
                tup[1]=otup[1]
            if tup[2] == None: #and otup[2] != None:
                tup[2]=otup[2]
            if tup[3] == None or tup[3] > otup[3]:
                tup[3]=otup[3]
            if tup[4] == None or tup[4] > otup[4]:
                tup[4]=otup[4]
            d[ut[0]]=tup
        return d
    def inherit_by_equality(d,k1,k2):
        changed=False
        t1=d[k1]
        t2=d[k2]
        if k1 != k2 and (k1 == t2[2] or k2 == t1[2]): # if they are equal
            if t1[0] != t2[0]:
                changed=True
                nval=max(t1[0],t2[0])
                t1[0]=nval
                t2[0]=nval
            if t1[1] != t2[1]:
                changed=True
                nval=max(t1[1],t2[1])
                t1[1]=nval
                t2[1]=nval
            if t1[3] != t2[3]:
                changed=True
                nval=min(t1[3],t2[3])
                t1[3]=nval
                t2[3]=nval
            if t1[4] != t2[4]:
                changed=True
                nval=max(t1[4],t2[4])
                t1[4]=nval
                t2[4]=nval
            d[k1]=t1
            d[k2]=t2
        return (d,changed)
    def inherit_while_possible(d):
        print "inherit_by_equality:"
        ks = d.keys()
        changed=False
        for k1 in ks:
            for k2 in ks:
                dnew,c = inherit_by_equality(d,k1,k2)
                changed= changed or c
                d=dnew
        if changed:
            return inherit_while_possible(d)
        else:
            return d
    def find_undefined_variable(d):
        for k in d.keys():
            t=d[k];
            # print "is none:",t[2] == None
            # print "is num:", t[2].is_numeric()
            # print "has no op:", t[2].operator() == None
            # print "is symb:", t[2].is_symbol()
            if t[2] == None or t[2].is_numeric() or (t[2].operator() == None and t[2].is_symbol()):
                return k
        return None
    def find_value_for(d,k):
        bound=d[k]
        val=None
        if bound[2] != None and bound[2].is_numeric():
            val=bound[2]
        elif bound[0] != None and bound[4] != None and bound[0].is_numeric() and bound[4].is_numeric():
            val=(bound[0] + bound[4])/2
        elif bound[1] != None and bound[3] != None and bound[1].is_numeric() and bound[3].is_numeric():
            #val=(bound[1] + bound[3])/2
            val=bound[1] # easier this way
        elif bound[0] != None and bound[0].is_numeric() and (bound[4] == None or bound[4].is_symbol()):
            val=bound[0] + 1
        elif bound[4] != None and bound[4].is_numeric() and (bound[0] == None or bound[0].is_symbol()):
            val=bound[4] - 1
        elif bound[1] != None and bound[1].is_numeric() and (bound[3] == None or bound[3].is_symbol()):
            val=bound[1]
        elif bound[3] != None and bound[3].is_numeric() and (bound[1] == None or bound[1].is_symbol()):
            val=bound[3]
        elif bound[0] == None and bound[1] == None and bound[3] == None and bound[4] == None:
            val=0
        else:
            val=None
        if val==None:
            return ([],[])
        else:
            repls=[(k,val)]
            #if bound[2].is_symbol():
            #    repls.append((bound[2],val))
            updates = []
            if bound[0] != None and bound[0].is_symbol():
                updates.append((bound[0],4,val))
            if bound[1] != None and bound[1].is_symbol():
                updates.append((bound[1],3,val))
            if bound[3] != None and bound[3].is_symbol():
                updates.append((bound[3],1,val))
            if bound[4] != None and bound[4].is_symbol():
                updates.append((bound[4],0,val))
            return (repls,updates)

    # def substitute_instances(d,subs_insts):
    #     def subs_bound_entry(be,k,val):
    #         if be == None:
    #             return (None,[])
    #         elif be.is_symbol()
    #     k,val=instance

    equation_tuples= list(itertools.chain(*map(equation_to_dict_tuple,equations)))
    eq_dict = reduce(update_tuples,equation_tuples,dict())
    inherit_eq_dict=inherit_while_possible(eq_dict)
    uv=find_undefined_variable(inherit_eq_dict)
    repls,updates=find_value_for(inherit_eq_dict,uv)
    print "found variable: ",uv
    print "  with bounds:",inherit_eq_dict[uv]
    print "  the following replacements were computed:",repls
    print "  and updates:", updates
    return


def solution_to_space(solution,coeff_vars,vec_vars):
    def eq_to_row(eq,vars):
        # print vars
        equals0 = eq.lhs() - eq.rhs()
        facts = map(lambda v:equals0.coefficient(v),vars)
        return facts
    def update_dict(v,t,d):
        td={v:t}
        # print td
        dnew = dict(map(lambda item:(item[0],item[1].substitute(d)),d.items()))
        dnew[v]=t
        return dnew
    # substitute coefficients to remove them.
    subs_dict=dict()
    for v in coeff_vars:
        for rel in solution:
            # print v,rel
            if rel.operator() == operator.eq:
                if rel.lhs() == v:
                    subs_dict=update_dict(v,rel.rhs(),subs_dict)
                if rel.rhs() == v:
                    subs_dict=update_dict(v,rel.lhs(),subs_dict)
    subs_solution=map(lambda rel:rel.substitute(subs_dict),solution)
    rows=[]
    for rel in subs_solution:
        # print rel
        if rel.operator() == operator.eq:
            rows.append(eq_to_row(rel,vec_vars))
    # return rows
    # convert to kernel space
    #print rows
    kspace = S.transpose(S.matrix(rows)).kernel()
    return kspace
