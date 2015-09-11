import term_braverman as T
import sage.all

def example_1():
    print "braverman exmaple 1, termination check"
    mB_s = matrix(ZZ,[[4,1],[8,2]])
    mB_w = matrix(ZZ,[[0,0]])
    mA = matrix(ZZ,[[-2,4],[4,0]])
    result = T.termination_check(mA,mB_s,mB_w)
    print "result:", result

def example_2():
    print "braverman example 2, termination check"
    mB_s = matrix(ZZ,[[4,-5]])
    mB_w = matrix(ZZ,[[0,0]])
    mA = matrix(ZZ,[[2,4],[4,0]])
    result = T.termination_check(mA,mB_s,mB_w)
    print "result:", result
    
def example_3():
    print "braverman example 3, find_Q_min test"
    t_Q_min=T.find_Q_min(VectorSpace(SR,3).subspace_with_basis([[1,0,sqrt(2)],[-sqrt(2),1,0]]),
        [QQbar(sqrt(2))])
    print "result:\n"+str(t_Q_min)
