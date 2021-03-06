
import sage.all as S
import term_braverman as T
import parse_example as E
import complexity as C

import sys
import time

def get_number_from(e):
    if isinstance(e,unicode):
        return S.sage_eval(e)
    else:
        return e

def lmatrix_to_numbers(mx):
    return map(lambda row: map(get_number_from,row),mx)


def run_example(filepath,more_info=False):
    e = E.Example(filepath)
    mA = S.matrix(S.QQ,lmatrix_to_numbers(e.matrix_A))
    mB_s = S.matrix(S.QQ,lmatrix_to_numbers(e.matrix_B_strict))
    mB_w = S.matrix(S.QQ,lmatrix_to_numbers(e.matrix_B_weak))
    print "Checking termination for example '"+ e.example_name +"'"
    print "published in " + e.published_in
    if more_info:
        print "Matrix A:"
        print mA
        print "Matrix jnf(A):"
        print mA.jordan_form(S.QQbar)
        print "Matrix B strict:"
        print mB_s
        print "Matrix B weak:"
        print mB_w
        print ("applicable to complexity theorem: " + str(C.are_absolute_eigenvalues_of_jordan_blocks_distinct(mA)))
        print ("polynomial update:                " + str(C.has_polynomial_growth(mA)))
        print ("max growth:                       " + str(C.pretty_growth(C.max_growth(mA))))
    sys.stdout.flush()
    start_time = time.time()
    result = T.termination_check(mA,mB_s,mB_w,more_info)
    end_time = time.time()
    print "result:",result
    print ("time: %0.4f seconds" % (end_time - start_time))
    print "-"*40+"\n"
    sys.stdout.flush()

if __name__ == '__main__':
    files = sys.argv[1:]
    print " ".join(sys.argv)
    sys.stdout.flush()
    for file in files:
        run_example(file,True)
