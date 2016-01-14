# -*- coding: utf-8 -*-

import sage.all as S


def are_absolute_eigenvalues_of_jordan_blocks_distinct(square_matrix):
    j = square_matrix.jordan_form(S.QQbar)
    number_of_blocks=len(j.subdivisions()[1]) + 1
    evs=set()
    for i in range(number_of_blocks):
        evs.add(j.subdivision(i,i)[0,0])
    aevs=set(map(abs,list(evs)))
    return len(evs) == len(aevs)

def has_polynomial_growth(square_matrix):
    j = square_matrix.jordan_form(S.QQbar)
    number_of_blocks=len(j.subdivisions()[1]) + 1
    is_poly=True
    for i in range(number_of_blocks):
        is_poly= is_poly and bool(abs(j.subdivision(i,i)[0,0]) <= 1)
    return is_poly

def max_growth(square_matrix):
    j = square_matrix.jordan_form(S.QQbar)
    number_of_blocks=len(j.subdivisions()[1]) + 1
    fastest_growing_block=j.subdivision(0,0)
    for i in range(1,number_of_blocks):
        b = j.subdivision(i,i)
        if (abs(b[0,0]) > abs(fastest_growing_block[0,0])) or (abs(b[0,0]) == abs(fastest_growing_block[0,0]) and b.dimensions()[0] > fastest_growing_block.dimensions()[0]):
            fastest_growing_block=b
    return (fastest_growing_block.dimensions()[0] - 1, abs(fastest_growing_block[0,0]))

def pretty_growth((p,e)):
    return ("O( n^("+str(p) + ") * (" + str(e) +")^n )")
