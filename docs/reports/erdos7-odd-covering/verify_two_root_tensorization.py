#!/usr/bin/env python3
"""Verify exact actual-layout tensorization for two fixed depth-two shapes.

Python 3.9+ standard library and NumPy only. No solver, network, external
project imports or absolute paths. Each shape is tested against itself for
all real nonnegative probability weights, by exact rational polytope reduction.
Every numerical comparison uses int64 and is covered by a checked overflow
bound. The mathematical reduction is in Problems/erdos-7-odd-covering-systems.md.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json
import numpy as np


SHAPES={
    '2+2':{'roots':((1,1,0,0),(0,0,1,1)),
           'polytope_sizes':(8,8,0,0,0,0,8,8),'vertices':15,'weight_sum_bound':27},
    '3+1':{'roots':((1,1,1,0),(0,0,0,1)),
           'polytope_sizes':(10,10,10,4,0,0,0,10),'vertices':18,'weight_sum_bound':40},
}
LEAVES=tuple(tuple(int(i==j) for i in range(4)) for j in range(4))
POSITIONS=tuple((i,j) for i in range(3) for j in range(3) if(i,j)!=(0,0))


def require(condition,message):
    if not condition:
        raise ValueError(message)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def null_vector(rows):
    return tuple((-1)**j*det3([[r[k] for k in range(4) if k!=j] for r in rows])
                 for j in range(4))


def gamma_polytope_vertices(local_forms,index):
    # x>=0, sum(x)=1, score_index(x)>=score_j(x) for every j.
    constraints=list(LEAVES)+[
        tuple(a-b for a,b in zip(local_forms[index],other)) for other in local_forms]
    vertices=set()
    for rows in combinations(constraints,3):
        vector=null_vector(rows)
        total=sum(vector)
        if total==0:
            continue
        point=tuple(F(x,total) for x in vector)
        if all(dot(row,point)>=0 for row in constraints):
            vertices.add(point)
    return sorted(vertices)


def verify_shape(name):
    config=SHAPES[name]
    roots=config['roots']
    parts={0:((1,1,1,1),),1:roots,2:LEAVES}
    local_forms=[tuple((1+r+t)**2 for r,t in zip(root,leaf))
                 for root,leaf in product(roots,LEAVES)]
    polytopes=[gamma_polytope_vertices(local_forms,i) for i in range(8)]
    require(tuple(map(len,polytopes))==config['polytope_sizes'],
            'local Gamma polytope size mismatch')
    vertices=sorted(set(point for polytope in polytopes for point in polytope))
    require(len(vertices)==config['vertices'],'rational vertex count mismatch')
    weights=[]
    for point in vertices:
        denominator=lcm(*(x.denominator for x in point))
        weight=tuple(int(x*denominator) for x in point)
        require(all(x>=0 for x in weight) and sum(weight)==denominator>0,
                'invalid integer vertex weights')
        weights.append(weight)
    largest_weight_sum=max(map(sum,weights))
    require(largest_weight_sum==config['weight_sum_bound'],
            'integer weight-sum bound mismatch')

    # There are nine divisors in each full two-coordinate depth-two window.
    # Every complete-layout load lies in [1,9], hence the second-moment
    # numerator is<=81*sum(x)*sum(y). Local Gamma products obey the same bound.
    integer_moment_bound=81*largest_weight_sum**2
    require(integer_moment_bound<np.iinfo(np.int64).max,'int64 overflow is possible')
    options=[np.array([np.outer(x,y).reshape(16)
                       for x,y in product(parts[i],parts[j])],dtype=np.int64)
             for i,j in POSITIONS]
    choices=np.array(list(product(*(range(len(option)) for option in options))),
                     dtype=np.int16)
    require(len(choices)==262144,'complete product-layout count mismatch')
    loads=np.ones((len(choices),16),dtype=np.int64)
    for k,option in enumerate(options):
        loads+=option[choices[:,k]]
    require(int(loads.min())>=1 and int(loads.max())<=9,'load-range bound failed')
    squared_loads=loads*loads
    pairs=list(product(range(len(weights)),repeat=2))
    for first in range(0,len(pairs),32):
        batch=pairs[first:first+32]
        product_weights=np.array([np.outer(weights[i],weights[j]).reshape(16)
                                  for i,j in batch],dtype=np.int64)
        values=squared_loads@product_weights.T
        maxima=values.max(axis=0)
        for column,((i,j),maximum) in enumerate(zip(batch,maxima)):
            expected=max(dot(row,weights[i]) for row in local_forms)*max(
                dot(row,weights[j]) for row in local_forms)
            maximum=int(maximum)
            require(maximum<=integer_moment_bound and expected<=integer_moment_bound,
                    'a moment exceeds the audited integer bound')
            if maximum>expected:
                layout=int(np.argmax(values[:,column]))
                raise ValueError(json.dumps({
                    'counterexample_shape':name,'weights_left':weights[i],
                    'weights_right':weights[j],'moment_numerator':maximum,
                    'Gamma_product_numerator':expected,'positions':POSITIONS,
                    'choices':choices[layout].tolist(),
                    'load_grid':loads[layout].reshape(4,4).tolist()}))
            # Product layouts attain the lower bound at every vertex pair.
            require(maximum==expected,'product-layout lower bound failed')
    return {'shape':name,'scope':'same-shape product; all real probability weights',
            'root_partition':[[i for i,b in enumerate(root) if b] for root in roots],
            'local_polytope_vertex_counts':list(map(len,polytopes)),
            'integer_vertex_weights':[list(row) for row in weights],
            'vertex_pair_count':len(pairs),'complete_layout_count':len(choices),
            'integer_comparison_count':len(pairs)*len(choices),
            'maximum_integer_weight_sum':largest_weight_sum,
            'integer_moment_upper_bound':integer_moment_bound}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shape',choices=('all','2+2','3+1'),default='all')
    args=parser.parse_args()
    data=json.loads(read_artifact_text(Path(__file__).resolve().parent / 'certificates/two_root_tensorization_certificate.json'))
    require(data.get('schema')=='two-root-depth-two-tensor-v1','certificate schema mismatch')
    require(set(data.get('shapes',{}))==set(SHAPES),'fixed shape set mismatch')
    names=tuple(SHAPES) if args.shape=='all' else (args.shape,)
    for name in names:
        result=verify_shape(name)
        require(result==data['shapes'][name],'fixed certificate differs from exact recomputation')
        print('Verified '+name+': '+str(result['integer_comparison_count'])+
              ' exact integer comparisons; moment numerators <= '+
              str(result['integer_moment_upper_bound'])+'.')


if __name__=='__main__':
    main()
