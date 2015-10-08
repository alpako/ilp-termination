
import sage.all as S
import term_braverman as T
import parse_example as E

import sys
import time

def get_number_from(e):
    if isinstance(e,unicode):
        return S.sage_eval(e)
    else:
        return e

def lmatrix_to_numbers(mx):
    return map(lambda row: map(get_number_from,row),mx)


def run_example(filepath):
    e = E.Example(filepath)
    mA = S.matrix(S.QQ,lmatrix_to_numbers(e.matrix_A))
    mB_s = S.matrix(S.QQ,lmatrix_to_numbers(e.matrix_B_strict))
    mB_w = S.matrix(S.QQ,lmatrix_to_numbers(e.matrix_B_weak))
    print "Checking termination for example '"+ e.example_name +"'"
    print "published in " + e.published_in
    print "Matrix A:"
    print mA
    print "Matrix jnf(A):"
    print mA.jordan_form(QQbar)
    print "Matrix B strict:"
    print mB_s
    print "Matrix B weak:"
    print mB_w
    start_time = time.time()
    result = T.termination_check(mA,mB_s,mB_w)
    end_time = time.time()
    print "result:",result
    print ("time: %s seconds" % (end_time - start_time))
    print "-"*40+"\n"

if __name__ == '__main__':
    files = sys.argv[1:]

    for file in files:
        run_example(file)
