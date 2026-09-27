#!/usr/bin/env python3
"""Actual all-odd irredundant noncover with every private prime-line covered.

The numerical moduli repeat: this is not an odd-distinct counterexample.
No SAT package, large class table, or Lean claim is needed for this control.
"""
from collections import Counter
from itertools import product
from math import prod
from pathlib import Path
import argparse,json

PATTERNS=(
    '**001','**010','*0*10','*0101','0*1*0','000*1',
    '001**','01*0*','010**','01111','10*00','100**',
    '10111','11000','11011','11100','11101','11110','11111',
)
PRIMES=(3,5,7,11,13)

def require(ok,msg):
    if not ok:raise ValueError(msg)

def member(pattern,word):
    return all(c=='*' or int(c)==a for c,a in zip(pattern,word))

def crt(values,primes):
    m=prod(primes)
    return sum(a*(m//p)*pow(m//p,-1,p) for a,p in zip(values,primes))%m,m

def run():
    words=list(product(range(2),repeat=5))
    bhits={w:[j for j,s in enumerate(PATTERNS) if member(s,w)] for w in words}
    bprivate=[[w for w,js in bhits.items() if js==[j]] for j in range(len(PATTERNS))]
    require([w for w,js in bhits.items() if not js]==[(0,)*5],'one Boolean hole')
    require(all(len(ws)==1 for ws in bprivate),'each Boolean pattern has exactly one private word')
    binary_neighbor_checks=0
    for ws in bprivate:
        w=ws[0]
        for k in range(5):
            changed=w[:k]+(1-w[k],)+w[k+1:];binary_neighbor_checks+=1
            require(bool(bhits[changed]),'all five neighbors of every Boolean private word covered')
    L=prod(PRIMES);labels=[];rows=[]
    for j,pattern in enumerate(PATTERNS):
        coords=[k for k,c in enumerate(pattern) if c!='*']
        ps=[PRIMES[k] for k in coords]
        choices=[(0,) if pattern[k]=='0' else range(1,PRIMES[k]) for k in coords]
        start=len(labels)
        for values in product(*choices):
            a,m=crt(values,ps);labels.append((m,a,j))
        rows.append({'pattern':pattern,'Boolean_private_word':''.join(map(str,bprivate[j][0])),
                     'modulus':prod(ps),'expanded_class_count':len(labels)-start})
    require(len({(m,a) for m,a,j in labels})==len(labels),'no identical AP copies')
    require(all(m>1 and m%2==1 and L%m==0 for m,a,j in labels),'all actual moduli odd nonunit divisors')
    multiplicity=[0]*L;unique_owner=[-1]*L
    for i,(m,a,j) in enumerate(labels):
        for x in range(a,L,m):multiplicity[x]+=1;unique_owner[x]=i
    holes=[x for x,c in enumerate(multiplicity) if not c]
    require(holes==[0],'one actual CRT hole')
    witness=[None]*len(labels);private_counts=[0]*len(PATTERNS);line_checks=0
    for x,c in enumerate(multiplicity):
        word=tuple(int(x%p!=0) for p in PRIMES)
        require(c==len(bhits[word]),'literal AP multiplicity equals Boolean pullback')
        if c!=1:continue
        i=unique_owner[x];witness[i]=x;private_counts[labels[i][2]]+=1
        for p in PRIMES:
            step=L//p
            for y in range(x%step,L,step):
                line_checks+=1;require(multiplicity[y]>0,'entire actual private prime-line covered')
    require(all(x is not None for x in witness),'EVERY expanded original AP has an actual private point')
    for row,n in zip(rows,private_counts):row['actual_private_point_count']=n
    duplicates={str(m):n for m,n in sorted(Counter(m for m,a,j in labels).items())}
    require(max(duplicates.values())>1,'essential scope defect: repeated numerical moduli')
    return {'scope':'Actual finite odd irredundant NONCOVER with every prime CRT line through every private point covered; numerical moduli REPEAT. Not an odd-distinct counterexample or a Lean result.',
            'primes':PRIMES,'period':L,'pattern_rows':rows,'Boolean_holes':['00000'],
            'Boolean_private_count':sum(map(len,bprivate)),'Boolean_overlap_count':sum(len(js)>1 for js in bhits.values()),
            'binary_neighbor_checks':binary_neighbor_checks,'actual_class_count':len(labels),
            'distinct_numerical_moduli':len(duplicates),'classes_per_modulus':duplicates,'actual_holes':holes,
            'actual_private_count':sum(private_counts),'actual_overlap_count':sum(c>1 for c in multiplicity),
            'actual_line_membership_checks':line_checks,'literal_multiplicity_checks':L,
            'all_expanded_APs_have_private_points':True,'all_private_prime_lines_covered':True}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
    out=run();args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in {'pattern_rows','classes_per_modulus'}},indent=2))
