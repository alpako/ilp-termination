
import sage.all as S
import term_braverman as T
import parse_example as E

import sys
import time

def run_example(filepath):
    e = E.Example(filepath)
    mA = S.matrix(S.ZZ,e.matrix_A)
    mB_s = S.matrix(S.ZZ,e.matrix_B_strict)
    mB_w = S.matrix(S.ZZ,e.matrix_B_weak)
    print "Checking termination for example '"+ e.example_name +"'"
    print "published in " + e.published_in
    print "Matrix A:"
    print mA
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
