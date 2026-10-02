#!/usr/bin/env python3
"""Fixed m=1,2,3 zero-tag grids for the two-cut rectangle excess theorem."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import json

P, Q, ELL = 3, 5, 7
MULTIPLICITIES = (1, 2, 3)

def crt(coords):
    x, modulus = 0, 1
    for a, n in coords:
        if n == 1:
            continue
        x += modulus * (((a-x)*pow(modulus,-1,n)) % n)
        modulus *= n
    return x % modulus

def valuation(n, p):
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result

def contains(label,x):
    return x % label['modulus'] == label['residue']

class Check:
    def __init__(self):
        self.count = 0
    def __call__(self,ok,message):
        self.count += 1
        if not ok:
            raise RuntimeError(message)

def family(m):
    labels = []
    for t in range(1,m+1):
        pp,qq=P**t,Q**(m+1-t)
        labels.append({'id':f'target:{t}','kind':'target','t':t,
                       'modulus':pp*qq,
                       'residue':crt(((P**(t-1),pp),(Q**(m-t),qq)))})
    k = 0
    for j in range(m+1):
        phases=[('zero',0,0)]
        if j >= 1:
            phases.extend((f'p:{c}',c*P**(j-1),0) for c in range(2,P))
        if j <= m-1:
            phases.extend((f'q:{c}',0,c*Q**(m-j-1)) for c in range(2,Q))
        for kind,a,b in phases:
            k += 1
            pp,qq,ee=P**j,Q**(m-j),ELL**k
            labels.append({'id':f'supplier:{j}:{kind}','kind':'supplier',
                           'j':j,'tag':k,'modulus':pp*qq*ee,
                           'residue':crt(((a,pp),(b,qq),(0,ee)))})
    return labels,k

def one_fixture(m,check):
    labels,K=family(m)
    pfull,qfull,efull=P**m,Q**m,ELL**K
    check(len({r['modulus'] for r in labels})==len(labels),'repeated numerical modulus')
    check(all(r['modulus']>1 and r['modulus']%2 for r in labels),'invalid odd original modulus')
    for ti in range(m):
        t=ti+1
        for i,label in enumerate(labels):
            if i != ti:
                check(valuation(label['modulus'],P)<t or valuation(label['modulus'],Q)<m+1-t,
                      'global cut failed')
    targets_private=[]
    for ti in range(m):
        t=ti+1
        x=crt(((P**(t-1),pfull),(Q**(m-t),qfull),(0,efull)))
        covering=[i for i,r in enumerate(labels) if contains(r,x)]
        check(covering==[ti],'target private CRT witness failed')
        targets_private.append({'target':t,'integer':x})
    hole=crt(((0,pfull),(1,qfull),(1,efull)))
    check(not any(contains(r,hole) for r in labels),'global CRT hole failed')

    # Only the zero-tag conditional grid is enumerated. The full period is not.
    points=[]
    for a in range(pfull):
        for b in range(qfull):
            x=crt(((a,pfull),(b,qfull),(0,efull)))
            mask=tuple(i for i,r in enumerate(labels) if contains(r,x))
            points.append((a,b,x,mask))
    check(len(points) in (15,225,3375),'grid outside explicit scope')
    groups=[]
    for ti in range(m):
        t=ti+1
        rows={}
        for a,b,x,mask in points:
            key=(a % P**(t-1), b % Q**(m-t))
            state=rows.setdefault(key,{'covered':True,'private':False})
            state['covered'] = state['covered'] and bool(mask)
            state['private'] = state['private'] or mask==(ti,)
        groups.append(rows)

    histogram=Counter()
    rectangle_counts=[0]*m
    total_excess=0
    zero=None
    for a,b,x,mask in points:
        memberships=[]
        for ti in range(m):
            t=ti+1
            g=groups[ti][(a % P**(t-1), b % Q**(m-t))]
            in_rectangle=(g['covered'] and g['private']
                          and a % P**t != P**(t-1)
                          and b % Q**(m+1-t) != Q**(m-t))
            memberships.append(in_rectangle)
            rectangle_counts[ti]+=in_rectangle
        multiplicity=sum(memberships)
        excess=max(len(mask)-1,0)
        check(multiplicity <= excess,'pointwise rectangle/excess inequality failed')
        histogram[(len(mask),multiplicity)] += 1
        total_excess += excess
        if a==0 and b==0:
            check(x==0 and multiplicity==m and len(mask)==m+1,'origin sharpness failed')
            zero={'rectangle_multiplicity':multiplicity,'covering_multiplicity':len(mask),
                  'covering_labels':[labels[i]['id'] for i in mask]}
    check(zero is not None,'origin missing')
    grid=len(points)
    return {
        'm':m,'p':P,'q':Q,'ell':ELL,'tag_height':K,
        'original_count':len(labels),'originals':labels,
        'conditional_grid_cells':grid,
        'private_target_witnesses':targets_private,
        'global_hole':hole,'origin':zero,
        'covered_private_fibre_counts':[sum(s['covered'] and s['private'] for s in g.values()) for g in groups],
        'rectangle_masses':[str(Fraction(n,grid)) for n in rectangle_counts],
        'sum_rectangle_mass':str(Fraction(sum(rectangle_counts),grid)),
        'excess_mass':str(Fraction(total_excess,grid)),
        'joint_multiplicity_histogram':[{'L':l,'rectangles':r,'cells':n} for (l,r),n in sorted(histogram.items())],
    }

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.output.exists():
        raise RuntimeError('Refusing to overwrite an existing result')
    check=Check()
    fixtures=[one_fixture(m,check) for m in MULTIPLICITIES]
    output={'status':'pass','checks':check.count,'fixtures':fixtures,
            'total_conditional_grid_cells':sum(r['conditional_grid_cells'] for r in fixtures),
            'scope':'Only m=1,2,3 at primes3,5,7; actual CRT memberships on zero-tag grids15,225,3375; no full-period scan, solver, extra parameters, or all-family computational claim.',
            'arithmetic':'Exact integer CRT and rational probabilities'}
    with args.output.open('x') as f:
        json.dump(output,f,indent=2)
        f.write('\n')
    print(json.dumps({'status':'pass','checks':check.count,'output':str(args.output),
                      'sha256':sha256(args.output.read_bytes()).hexdigest(),
                      'fixtures':[{k:r[k] for k in ('m','conditional_grid_cells','sum_rectangle_mass','excess_mass')} for r in fixtures]}))

if __name__=='__main__':
    main()
