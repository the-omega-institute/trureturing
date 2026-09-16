#!/usr/bin/env python3
"""Replay the fixed-K33 max-plus price-family obstruction using integers.

No optimizer, C++ executable, NumPy, or sampled-profile completeness is used.
Every retained B and grouped kernel is replayed as literal congruence classes.
Their finite epigraph is a LOWER relaxation of the best global majorant.
A sparse rational dual, with exact box-residual correction, proves that its
minimum already exceeds the target. This does not lower-bound an actual moment
and does not exclude using another reference K.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm
from pathlib import Path
import argparse,json

HERE=Path(__file__).resolve().parent
DEFAULT_SOURCE=HERE

def require(ok,message):
    if not ok:raise ArithmeticError(message)

def mul(values):
    out=F(1)
    for v in values:out*=v
    return out

class Matrix:
    def __init__(self):self.cost=[];self.rows=[];self.rhs=[]
    def variable(self,cost=0):
        self.cost.append(cost);return len(self.cost)-1
    def inequality(self,terms,rhs=0):
        self.rows.append(dict(terms));self.rhs.append(rhs)

def evaluate(data,source):
    names=('mod3_conditioned_geometry_certificate.json','original9_conditioned_geometry_certificate.json')
    raw={name:(source/name).read_bytes() for name in names}
    require(data['source_sha256']=={name:sha256(value).hexdigest() for name,value in raw.items()},
            'canonical probability and previous-bound source hashes')
    case=next(c for c in json.loads(raw[names[0]])['cases'] if c['name']=='PG1')
    m9=json.loads(raw[names[1]])['result']
    points,weights=case['points'],case['weight_numerators'];den=case['weight_denominator'];n=len(points)
    require(n==75 and len(weights)==75 and sum(weights)==den==1000000007 and min(weights)>=0 and
            points==[t for t in range(315) if all(t%d!=a for d,a in case['family'])], 'same actual PG1 probability')
    require(data['schema']=='pg1-fixed-reference-maxplus-price-obstruction-v1' and data['reference']==33,
            'fixed reference and certificate schema')
    K=33;scale=48*den
    exponents=list(product(range(3),range(2),range(2)))
    ds=[3**a*5**b*7**c for a,b,c in exponents]
    sat={d:{p for p,h,e in zip((3,5,7),(2,1,1),abc) if h==e} for d,abc in zip(ds,exponents)}
    aa={d:mul(F(p,p-1) for p in sat[d]) for d in ds}
    gamma={d:aa[d]-1 for d in ds}
    remaining={d:gamma[d]-(F(1,2) if d in (9,45) else 0)
                  -(F(1,4) if d in (5,15,45) else 0)
                  -(F(1,6) if d%7==0 else 0)-(F(1,4) if d==35 else 0) for d in ds}
    require(min(gamma.values())>=0 and min(remaining.values())>=0,'nonnegative auxiliary coefficients')
    masks={d:[[int(t%d==a) for t in points] for a in range(d)] for d in ds}
    caps={d:max(sum(w*v for w,v in zip(weights,mask)) for mask in masks[d]) for d in ds}
    high=F()
    for d,e in product(ds,repeat=2):
        bb=mul(F(p*(p+1),(p-1)**2) if p in sat[d]&sat[e] else F(p,p-1) for p in sat[d]|sat[e])
        kappa=bb-aa[d]-aa[e]+1
        require(kappa>=0,'nonnegative higher-label pair coefficient')
        high+=kappa*F(caps[lcm(d,e)],den)
    terms=[('moment',d,2*gamma[d]) for d in ds if gamma[d]]
    terms += [('remaining',d,remaining[d]) for d in ds if remaining[d]]
    terms += [('group',None,F(1))]
    coefficients=[];qmax=[]
    for kind,d,a in terms:
        rows=[]
        for w in weights:
            row=[48*a*w*(k if kind=='moment' else max(K-k*k,0)) for k in range(1,13)]
            require(all(v.denominator==1 for v in row),'integer scaled potential')
            rows.append(list(map(int,row)))
        coefficients.append(rows);qmax.append([max(row) for row in rows])
    B_set=set()
    for labels in data['low_test_witnesses']:
        require(len(labels)==12 and sorted(r['modulus'] for r in labels)==sorted(ds) and
                all(type(r['residue']) is int and 0<=r['residue']<r['modulus'] for r in labels),
                'one actual original class per divisor')
        B=tuple(sum(int(t%r['modulus']==r['residue']) for r in labels) for t in points)
        require(B not in B_set,'distinct B witness');B_set.add(B)
    group_set=set()
    for w in data['group_witnesses']:
        require(len(w['A_residues'])==2 and len(w['B_residues'])==3 and len(w['E7_residues'])==6,
                'complete group witness')
        residues=list(zip((9,45),w['A_residues']))+list(zip((5,15,45),w['B_residues']))+[(35,w['extra_residue'])]+list(zip((7,21,35,63,105,315),w['E7_residues']))
        require(all(type(a) is int and 0<=a<d for d,a in residues),'valid group cylinders')
        profile=[]
        for t in points:
            A=sum(int(t%d==a) for d,a in zip((9,45),w['A_residues']))
            D=sum(int(t%d==a) for d,a in zip((5,15,45),w['B_residues']))+int(t%35==w['extra_residue'])
            C=sum(int(t%d==a) for d,a in zip((7,21,35,63,105,315),w['E7_residues']))
            profile.append(24*A+12*D-6*A*D+(2-A)*(4-D)*C)
        require(min(profile)>=0 and max(profile)<=48 and tuple(profile) not in group_set,
                'distinct group kernel in unit interval')
        group_set.add(tuple(profile))
    model=Matrix();nj=len(terms)
    q=[[model.variable() for i in range(n)] for j in range(nj)]
    h=[[[model.variable() for k in range(12)] for i in range(n)] for j in range(nj)]
    for j in range(nj):
        for i in range(n):
            maximum=qmax[j][i]
            for k in range(12):
                model.inequality(((q[j][i],-maximum),(h[j][i][k],-maximum)),-coefficients[j][i][k])
    Bmax=144*scale+sum(sum(row) for row in qmax);tb=model.variable(-Bmax)
    for B in sorted(B_set):
        entries=[(tb,-Bmax)]
        for j in range(nj):entries.extend((h[j][i][k-1],qmax[j][i]) for i,k in enumerate(B))
        model.inequality(entries,-sum(48*w*b*b for w,b in zip(weights,B)))
    for j,(kind,d,a) in enumerate(terms):
        if kind!='group':
            maximum=max(sum(q*v for q,v in zip(qmax[j],mask)) for mask in masks[d]);eta=model.variable(-maximum)
            for mask in masks[d]:
                model.inequality([(eta,-maximum)]+[(q[j][i],qmax[j][i]) for i in range(n) if mask[i]])
        else:
            maximum=sum(qmax[j]);eta=model.variable(-maximum)
            for profile in sorted(group_set):
                model.inequality([(eta,-48*maximum)]+[(q[j][i],qmax[j][i]*a) for i,a in enumerate(profile) if a])
    dimensions={'B_witnesses':len(B_set),'group_witnesses':len(group_set),
                'variables':len(model.cost),'inequalities':len(model.rows)}
    require(dimensions==data['model_dimensions'],'exact finite lower model dimensions')
    D=data['dual_denominator'];require(type(D) is int and D>0,'positive dual denominator')
    sparse=data['dual_sparse'];indices=[entry[0] for entry in sparse]
    require(indices==sorted(set(indices)) and all(type(i) is int and 0<=i<len(model.rows) and
                type(v) is int and v>0 for i,v in sparse),'nonnegative sparse dual')
    residual=[c*D for c in model.cost];base=0
    for i,multiplier in sparse:
        base+=model.rhs[i]*multiplier
        for j,a in model.rows[i].items():residual[j]-=a*multiplier
    correction=sum(max(v,0) for v in residual)
    # This bounds max(-epigraph_objective). Negating yields its minimum's lower bound.
    lower=high-F(base+correction,scale*D)
    target=K+F(m9['survival_lower'])*(F(m9['Gamma_upper'])-K)
    require(base==data['dual_base'] and correction==data['positive_residual'] and
            str(lower)==data['price_family_lower'],'exact integer dual and full box residual')
    require(str(target)==data['functional_target_to_improve_head'] and lower>target,
            'fixed-reference price family cannot improve the existing head bound')
    return lower,target,dimensions

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=HERE/'pg1_maxplus_obstruction_certificate.json')
    parser.add_argument('--source-dir',type=Path,default=DEFAULT_SOURCE)
    args=parser.parse_args();data=json.loads(args.certificate.read_text())
    lower,target,dimensions=evaluate(data,args.source_dir)
    print(json.dumps({'result':'verified','reference':33,'price_family_lower':str(lower),
                      'improvement_target':str(target),'strict_gap':str(lower-target),
                      'dimensions':dimensions}))

if __name__=='__main__':main()
