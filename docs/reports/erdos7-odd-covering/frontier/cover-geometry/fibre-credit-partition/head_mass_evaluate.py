"""Evaluate two documented fixed witness schemas at gamma=1/2.

Exact old joint, zero-row, and supported-head min-cap fees. No search.
Only explicitly supplied witness paths and the output path are accessed.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

HEADS=(5,7)
PRIVATE=(11,13,17,19,23,29,31,37,41)
PRIMES=HEADS+PRIVATE
ROOTS=(1,2)
EXPECTED_OLD={
    'first_layer_witness':F(3248409174919,118989428307750),
    'bounded_joint_result':F(5402534297581,198315713846250),
}


def multiply(values):
    return prod(values,start=F(1))


class Checks:
    def __init__(self):
        self.count=0

    def require(self,condition,message):
        self.count+=1
        if not condition:
            raise ValueError(message)


def identify_schema(data):
    if all(k in data for k in ('minimum_found','final_rows','final_masks','gamma')):
        if data['gamma']!='1/2':
            raise ValueError('bounded_joint_result must have gamma=1/2')
        return 'bounded_joint_result'
    if all(k in data for k in ('first_layer_star','common_rows','masks','objectives')):
        return 'first_layer_witness'
    raise ValueError('Unsupported witness schema; expected first_layer_witness or bounded_joint_result')


def read_witness(path,check):
    raw=Path(path).read_bytes()
    data=json.loads(raw)
    schema=identify_schema(data)
    check.require(tuple(data['private_primes'])==PRIVATE,'Declared nine private primes and ordering')
    c={p:F(p-1,p-2) for p in PRIMES}
    b={p:F(1,p-2) for p in PRIMES}
    w={r:{p:tuple(F(v) for v in data['head_weights'][str(r)][str(p)])
          for p in HEADS} for r in ROOTS}
    arrays={r:{p:tuple(tuple(F(v) for v in row) for row in data['arrays'][str(r)][str(p)])
               for p in HEADS} for r in ROOTS}
    g={r:{q:F(1) if r==1 else 1-b[q] for q in PRIVATE} for r in ROOTS}
    for p in HEADS:
        ell=tuple(F(v) for v in data['common_head_laws'][str(p)])
        check.require(len(ell)==p and sum(ell)==1 and all(0<=v<=c[p]/p for v in ell),
                      'Shared capped physical head law')
        for r in ROOTS:
            loss=tuple(F(v) for v in data['head_star_losses'][str(r)][str(p)])
            check.require(len(w[r][p])==p and len(loss)==p,'Complete physical head rows retained')
            check.require(all(0<=m<=v and v-m==z for v,m,z in zip(ell,loss,w[r][p])),
                          'Head weights reconstructed from common law and root-specific loss')
            g[r][p]=sum(w[r][p])
            check.require(g[r][p]>0,'Positive head carrier for the two fixed witnesses')
            check.require(len(arrays[r][p])==len(PRIVATE) and all(len(row)==p for row in arrays[r][p]),
                          'Raw projection array dimensions')
    for t,q in enumerate(PRIVATE):
        for p in HEADS:
            record=data['private_sources'][str(q)][str(p)]
            free=tuple(F(v) for v in record['free'])
            selected={r:tuple(F(v) for v in record['selected_increment'][str(r)]) for r in ROOTS}
            check.require(len(free)==p and all(len(selected[r])==p for r in ROOTS),'Shared private row dimensions')
            check.require(all(v>=0 for v in free) and sum(free)<=b[q],'Common free original cap budget')
            check.require(all(v>=0 for r in ROOTS for v in selected[r]) and
                          sum(sum(selected[r]) for r in ROOTS)<=b[q],'Selected allowance charged once globally')
            for r in ROOTS:
                check.require(all(g[r][q]*arrays[r][p][t][i]==free[i]+selected[r][i]
                                  for i in range(p)),
                              'Actual raw arrays reconstructed from same surviving free mass and selected increments')
                check.require(all(0<=free[i]+selected[r][i]<=g[r][q] for i in range(p)),
                              'Within-row actual private survivor mass cap')
        check.require(5*b[q]<=1,'Disjoint private role bands plus star fit one common probability source')
        for r in ROOTS:
            check.require(sum(arrays[r][5][t])+sum(arrays[r][7][t])<=1,
                          'Unclipped raw budget guard for group residual')
    return data,schema,c,b,w,arrays,g,sha256(raw).hexdigest()


def threshold(p,lower,c,w):
    positive=[v for r in ROOTS for v in w[r][p] if v>0]
    n=lower
    if positive:
        smallest=min(positive)
        while c[p]/p**n>smallest:
            n+=1
    return n


def geometric_labels(p,lower,c,w):
    n=threshold(p,lower,c,w)
    return [(e,F(1)) for e in range(lower,n)]+[(n,F(p,p-1))]


def supported_head_sum(fixed,table,lower,c,w):
    """HM10: exact sum of per-depth free/selected maxima, tails included."""
    free,selected=F(0),F(0)
    axes=[geometric_labels(p,lower[p],c,w) for p in fixed]
    for cell in product(*axes):
        depths={p:e for p,(e,_) in zip(fixed,cell)}
        factor=multiply(weight for _,weight in cell)
        candidates=[]
        for address,T in table.items():
            row=dict(zip(fixed,address))
            v=tuple(T[r]*multiply(min(c[p]/p**depths[p],w[r][p][row[p]]) for p in fixed)
                    for r in ROOTS)
            candidates.append(((v[0]+v[1])/2,max(v)/2))
        free+=factor*max(v[0] for v in candidates)
        selected+=factor*max(v[1] for v in candidates)
    return free,selected


def evaluate(path):
    check=Checks()
    data,schema,c,b,w,arrays,g,digest=read_witness(path,check)
    full=(1<<len(PRIVATE))-1
    # Product over exactly the unsupported private coordinates, on each head cell.
    matrices={}
    out_g={}
    residual={}
    for r in ROOTS:
        factors=[[[g[r][q]*(1-max(arrays[r][5][t][i],arrays[r][7][t][j]))
                   for j in range(7)] for i in range(5)] for t,q in enumerate(PRIVATE)]
        matrices[r]=[[[F(1) for _ in range(7)] for _ in range(5)]]
        out_g[r]=[F(1)]
        for mask in range(1,full+1):
            bit=mask & -mask
            t=bit.bit_length()-1
            previous=mask^bit
            matrices[r].append([[matrices[r][previous][i][j]*factors[t][i][j]
                                 for j in range(7)] for i in range(5)])
            out_g[r].append(out_g[r][previous]*g[r][PRIVATE[t]])
        residual[r]=multiply(g[r][q] for q in PRIVATE)*sum(
            w[r][5][i]*w[r][7][j]*multiply(
                1-arrays[r][5][t][i]-arrays[r][7][t][j] for t in range(len(PRIVATE)))
            for i,j in product(range(5),range(7)))
        if schema=='first_layer_witness':
            carrier=multiply(g[r][p] for p in PRIMES)
            check.require(residual[r]==carrier-F(data['objectives'][str(r)]),
                          'Group residual reproduces stored first-layer objective')
    modes=('old_joint','zero_row','head_min')
    totals={mode:{'free':F(0),'selected':F(0)} for mode in modes}
    buckets={}
    strict={'zero_free':0,'zero_selected':0,'min_free':0,'min_selected':0}
    support_count=0
    for size in range(2,len(PRIMES)+1):
        for support in combinations(PRIMES,size):
            fixed=tuple(p for p in HEADS if p in support)
            inside=sum(1<<t for t,q in enumerate(PRIVATE) if q in support)
            outside=full^inside
            lower={p:2 if size==2 and len(fixed)==1 else 1 for p in fixed}
            private_factor=multiply(b[q] for q in PRIVATE if q in support)
            head_inventory=multiply(c[p]*F(1,p**lower[p])*F(p,p-1) for p in fixed)
            R=private_factor*head_inventory
            old_R=multiply(b[p] for p in support)
            if size==2 and len(fixed)==1:
                p=fixed[0]
                q=next(q for q in PRIVATE if q in support)
                old_R=(b[p]-c[p]/p)*b[q]
            check.require(R==old_R,'HM6 same nongroup inventory with shallow head-private removal only')
            table={}
            for address in product(*(range(p) for p in fixed)):
                row=dict(zip(fixed,address))
                T={}
                for r in ROOTS:
                    value=sum((F(1) if 5 in fixed else w[r][5][i])*
                              (F(1) if 7 in fixed else w[r][7][j])*
                              matrices[r][outside][i][j]
                              for i in ([row[5]] if 5 in fixed else range(5))
                              for j in ([row[7]] if 7 in fixed else range(7)))
                    old_marginal=out_g[r][outside]*multiply(g[r][p] for p in HEADS if p not in fixed)
                    check.require(0<=value<=old_marginal,'Actual unsupported-coordinate table bounded by old marginal fee')
                    T[r]=value
                table[address]=T
            old_free=R*max((T[1]+T[2])/2 for T in table.values())
            old_selected=R*max(T[r]/2 for T in table.values() for r in ROOTS)
            zero_candidates=[]
            for address,T in table.items():
                row=dict(zip(fixed,address))
                z=tuple(T[r]*int(all(w[r][p][row[p]]>0 for p in fixed)) for r in ROOTS)
                zero_candidates.append(((z[0]+z[1])/2,max(z)/2))
            zero_free=R*max(v[0] for v in zero_candidates)
            zero_selected=R*max(v[1] for v in zero_candidates)
            summed=supported_head_sum(fixed,table,lower,c,w)
            min_free,min_selected=(private_factor*v for v in summed)
            check.require(0<=min_free<=zero_free<=old_free,'Every support: min <= zero-row <= old-joint free fee')
            check.require(0<=min_selected<=zero_selected<=old_selected,'Every support: min <= zero-row <= old-joint selected-once fee')
            strict['zero_free']+=int(zero_free<old_free)
            strict['zero_selected']+=int(zero_selected<old_selected)
            strict['min_free']+=int(min_free<zero_free)
            strict['min_selected']+=int(min_selected<zero_selected)
            values={'old_joint':(old_free,old_selected),'zero_row':(zero_free,zero_selected),
                    'head_min':(min_free,min_selected)}
            key=','.join(map(str,fixed)) or 'none'
            bucket=buckets.setdefault(key,{'support_count':0,**{
                mode:{'free':F(0),'selected':F(0)} for mode in modes}})
            bucket['support_count']+=1
            for mode,(free,selected) in values.items():
                totals[mode]['free']+=free
                totals[mode]['selected']+=selected
                bucket[mode]['free']+=free
                bucket[mode]['selected']+=selected
            support_count+=1
    check.require(support_count==2036,'All complete mixed supports accounted for')
    weighted_residual=(residual[1]+residual[2])/2
    for mode in modes:
        totals[mode]['score']=weighted_residual-totals[mode]['free']-totals[mode]['selected']
    check.require(totals['old_joint']['score']==EXPECTED_OLD[schema],
                  'Reproduce predeclared exact old-joint fixed-array score')
    if schema=='bounded_joint_result':
        expected=data['minimum_found']['values']
        check.require(weighted_residual==F(expected['residual']) and
                      all(totals['old_joint'][k]==F(expected[k]) for k in ('free','selected','score')),
                      'All four old-joint components reproduce stored bounded-result arrays')
    check.require(totals['old_joint']['score']<=totals['zero_row']['score']<=totals['head_min']['score'],
                  'Global same-array comparison ordering')
    return {
        'witness_path':str(path),'witness_sha256':digest,'recognized_schema':schema,
        'gamma':'1/2','root_group_residuals':{str(r):str(residual[r]) for r in ROOTS},
        'weighted_group_residual':str(weighted_residual),
        'modes':{mode:{**{k:str(v) for k,v in totals[mode].items()},
                       'score_decimal':float(totals[mode]['score'])} for mode in modes},
        'gain_zero_over_old':str(totals['zero_row']['score']-totals['old_joint']['score']),
        'gain_min_over_zero':str(totals['head_min']['score']-totals['zero_row']['score']),
        'head_tail_start_at_lower_one':{str(p):threshold(p,1,c,w) for p in HEADS},
        'support_count':support_count,'strict_support_improvements':strict,
        'by_supported_heads':{key:{'support_count':bucket['support_count'],**{
            mode:{k:str(v) for k,v in bucket[mode].items()} for mode in modes}}
            for key,bucket in buckets.items()},
        'checks':check.count,
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--witness',action='append',required=True,
                        help='Explicit first_layer_witness or bounded_joint_result JSON; may repeat.')
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    results=[evaluate(path) for path in args.witness]
    output={
        'schema_version':1,
        'contract':'Fixed gamma=1/2 evaluation of the documented first-layer baseline and bounded-result schemas. Exact HM7/HM10 head-depth sums; no array or weight search and no uniform positivity claim.',
        'results':results,'checks':sum(result['checks'] for result in results),
        'limits':[
            'Arrays are validated against their stored abstract common-source free and selected masses; arithmetic realization is not asserted.',
            'Every support sums per-depth address/root maxima; it does not exchange an infinite sum and a maximum.',
            'The baseline and bounded-result old-joint scores are checked against the two predeclared exact values.',
            'All three comparisons use the same actual stored head weights, grouped arrays, source factors and numerical inventory.',
            'No array or root-weight search, imported experiment code or Lean verification.',
        ],
    }
    Path(args.output).write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'checks':output['checks'],'results':[
        {'schema':r['recognized_schema'],'scores':{m:v['score_decimal'] for m,v in r['modes'].items()}}
        for r in results]},sort_keys=True))


if __name__=='__main__':
    main()
