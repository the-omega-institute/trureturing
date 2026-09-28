#!/usr/bin/env python3
"""Exact finite certificates for Context Geometry section 89.

Python >=3.10, standard library; requires companion verify.py. Run from any
working directory, optionally with --output PATH. Checks separate unnormalized
branch spans and specified quotients, not a general proof or physical costs.
"""
import argparse
from fractions import Fraction as Q
import importlib.util
from itertools import product, combinations
import json
from math import prod
from pathlib import Path

if not __debug__:
    raise RuntimeError('Exact checks require assertions.')
helper = Path(__file__).with_name('verify.py')
spec = importlib.util.spec_from_file_location('two51_filter_helpers', helper)
if spec is None or spec.loader is None:
    raise ImportError('Cannot load the companion exact linear algebra helpers.')
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
rank, local_basis = h.rank, h.local_basis


def tensor_basis(dims):
    points = list(product(*(range(n) for n in dims)))
    bases = [local_basis(n) for n in dims]
    vectors = []
    for s in product(*(range(n) for n in dims)):
        if sum(v != 0 for v in s) >= 2:
            vectors.append([prod(bases[i][s[i]][x[i]] for i in range(len(dims))) for x in points])
    return points, vectors


def closure(dims):
    points, vectors = tensor_basis(dims)
    n = len(points)
    marginals = [[int(x[i] == a) for x in points] for i,d in enumerate(dims) for a in range(d)]
    assert rank(marginals) == 1 + sum(d-1 for d in dims)
    assert rank(vectors) == n-rank(marginals)
    assert all(sum(x*y for x,y in zip(v,m)) == 0 for v in vectors for m in marginals)
    def filtered(v, ij, ab):
        return [t if all(x[i]==a for i,a in zip(ij,ab)) else 0 for t,x in zip(v,points)]
    singles, single_images = [], []
    for i,d in enumerate(dims):
        images = [filtered(v,(i,),(a,)) for a in range(d) for v in vectors]
        expected = n-d
        assert rank(images) == expected
        assert all(sum(t for t,x in zip(v,points) if x[i]==a)==0 for v in images for a in range(d))
        # Full recorded instrument preserves every original vector, hence its
        # dim(K) joint image is distinct from the (N - n_i)-dimensional hull.
        joint = [[t for a in range(d) for t in filtered(v,(i,),(a,))] for v in vectors]
        assert rank(joint) == len(vectors)
        singles.append(expected)
        single_images.append(images)
    pairs = {}
    for i,j in combinations(range(len(dims)),2):
        images = [filtered(v,(i,j),(a,b)) for a in range(dims[i]) for b in range(dims[j]) for v in vectors]
        assert rank(images) == n
        assert rank(single_images[i]+single_images[j]) == n-1
        pairs[f'{i},{j}'] = n
    return {'dimensions':dims,'source':n,'kernel':len(vectors),'one_filter_hulls':singles,
            'two_filter_hulls':pairs,'two_family_one_step_span':n-1,
            'recorded_instrument_image':len(vectors)}


def quotient_checks():
    size = 55
    unit = lambda i: [int(k==i) for k in range(size)]
    def tensor(u,j): return [u[a]*int(k==j) for a in range(5) for k in range(11)]
    ub=local_basis(5)
    nk=[tensor(ub[0],j) for j in range(4)]
    nv=[tensor(ub[a],10) for a in range(1,5)]
    def qk(v):
        return [v[11*a+j]-v[44+j] for a in range(4) for j in range(4)] + [v[11*a+j] for a in range(5) for j in range(4,11)]
    def qv(v):
        return [v[11*a+j] for a in range(5) for j in range(10)] + [sum(v[11*a+10] for a in range(5))]
    def branch(v,a): return [t if k//11==a else 0 for k,t in enumerate(v)]
    def recoverk(y):
        return [(y[a][4*a+j] if a < 4 else -y[4][j]) if j < 4
                else y[a][16+7*a+j-4] for a in range(5) for j in range(11)]
    def recoverv(y):
        return [y[a][10*a+j] if j < 10 else y[a][50]
                for a in range(5) for j in range(11)]
    def sectionk(y):
        return [(y[4*a+j] if a < 4 else 0) if j < 4 else y[16+7*a+j-4]
                for a in range(5) for j in range(11)]
    def sectionv(y):
        return [y[10*a+j] if j < 10 else (y[50] if a == 4 else 0)
                for a in range(5) for j in range(11)]
    def shifted(v): return v[-11:]+v[:-11]
    def recorded(q,v): return [q(branch(v,a)) for a in range(5)]
    def selected_record(y,b):
        return [row if a == b else [0]*51 for a,row in enumerate(y)]
    def shifted_record(q,section,y):
        return [q(shifted(section(y[(a-1)%5]))) for a in range(5)]
    # Exact left inverses and operation intertwining on all55 basis vectors.
    # Neither inverse claims to be a recovery from just the old51-vector q(v).
    for q,recover,section in [(qk,recoverk,sectionk),(qv,recoverv,sectionv)]:
        for e in h.eye(51):
            assert q(section(e)) == e
        for i in range(size):
            v=unit(i)
            y=recorded(q,v)
            assert recover(y) == v
            assert recorded(q,shifted(v)) == shifted_record(q,section,y)
            for b in range(5):
                assert recorded(q,branch(v,b)) == selected_record(y,b)
    def forward(y): return recorded(qv,recoverk(y))
    def backward(y): return recorded(qk,recoverv(y))
    for i in range(size):
        v=unit(i)
        yk,yv=recorded(qk,v),recorded(qv,v)
        assert forward(yk) == yv and backward(yv) == yk
        assert backward(forward(yk)) == yk and forward(backward(yv)) == yv
        assert forward(shifted_record(qk,sectionk,yk)) == shifted_record(qv,sectionv,yv)
        assert backward(shifted_record(qv,sectionv,yv)) == shifted_record(qk,sectionk,yk)
        for b in range(5):
            assert forward(selected_record(yk,b)) == selected_record(yv,b)
            assert backward(selected_record(yv,b)) == selected_record(yk,b)
    quotients = []
    constraint_spaces = []
    for name,nk0,q in [('K',nk,qk),('V',nv,qv)]:
        assert rank(nk0) == 4 and all(not any(q(v)) for v in nk0)
        assert rank([q(unit(i)) for i in range(size)]) == 51
        failures = [any(any(q(branch(v,a))) for v in nk0) for a in range(5)]
        assert all(failures)
        refined = [[t for a in range(5) for t in q(branch(unit(i),a))] for i in range(size)]
        assert rank(refined) == 55
        generated = [branch(v,a) for v in nk0 for a in range(5)]
        grank=rank(generated)
        assert grank == (20 if name=='K' else 5)
        # Linear equations in all25 entries of A for q (A tensor I) N=0.
        equations=[]
        for v in nk0:
            output_columns=[]
            for r,c in product(range(5),repeat=2):
                out=[v[11*c+j] if a==r else 0 for a in range(5) for j in range(11)]
                output_columns.append(q(out))
            equations.extend([list(row) for row in zip(*output_columns)])
        constraint_spaces.append(equations)
        quotients.append({'name':name,'quotient_rank':51,'refined_rank':55,
                          'individual_filter_failures':failures,'diagonal_generated_kernel_rank':grank,
                          'branch_constraint_rank':rank(equations)})
    both=sum(constraint_spaces,[])
    expected=[]
    for i in range(1,5):
        expected.append([int(a==i)-int(a==0) for a,b in product(range(5),repeat=2)])
        expected.append([int(b==i)-int(b==0) for a,b in product(range(5),repeat=2)])
    assert rank(both) == rank(expected) == rank(both+expected) == 8
    # Both subspace constraints have exactly the same17-dimensional solution
    # space as constant row/column sums. Equality of their constants follows
    # from summing entries. A nonnegative diagonal member is necessarily cI.
    diagonal_equations=[[eq[6*i] for i in range(5)] for eq in both]
    assert rank(diagonal_equations)==4
    # A different four-dimensional kernel can descend through all filters.
    # It privileges position0 and fails invariance under the five-cycle.
    privileged = [unit(j) for j in range(4)]
    def qp(v): return v[4:]
    assert rank([qp(unit(i)) for i in range(size)]) == 51
    assert all(not any(qp(branch(v,a))) for v in privileged for a in range(5))
    assert rank([[t for a in range(5) for t in qp(branch(unit(i),a))]
                 for i in range(size)]) == 51
    shifted = privileged[0][-11:] + privileged[0][:-11]
    assert any(qp(shifted))
    return {'quotients':quotients,'common_constraint_rank':8,
            'privileged_quotient_refined_rank':51,
            'response_bridge':{'basis_vectors':55,'nominal_response_coordinates':255,
                               'filter_operations':5,'inverse_directions':2,
                               'cycle_intertwining':True},
            'common_operator_space_dimension':17,'diagonal_operator_space_dimension':1}


def stochastic_fixture():
    # Source-independent labels can coexist with invertible post-branch states.
    matrices = [h.scale(h.eye(5), Q(1,2)),
                [[Q(int(i == (j+1)%5),2) for j in range(5)] for i in range(5)],
                [[Q(0) for _ in range(5)] for _ in range(5)]]
    probabilities = [Q(1,2),Q(1,2),Q(0)]
    for a,c in zip(matrices,probabilities):
        assert all(x >= 0 for row in a for x in row)
        assert all(sum(row) == c for row in a)
        assert all(sum(a[i][j] for i in range(5)) == c for j in range(5))
    assert sum(probabilities) == 1
    assert h.power(h.scale(matrices[1],2),5) == h.eye(5)
    return {'outcome_probabilities':list(map(str,probabilities)),
            'conditional_cycle_order':5, 'zero_weight_branch':2,
            'scope':'Specific mixture of identity, five-cycle, and zero branch.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result={'arithmetic':'exact rational row reduction',
            'closures':[closure(d) for d in [(2,2),(3,2,2),(5,3,2,2)]],
            'quotient_checks':quotient_checks(),
            'stochastic_fixture':stochastic_fixture(),
            'scope':'Separate unnormalized branch spans and specified quotient kernels; joint-image and operator-space dimensions are distinct.'}
    data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(data,encoding='utf-8')
    else:
        print(data,end='')

if __name__=='__main__': main()
