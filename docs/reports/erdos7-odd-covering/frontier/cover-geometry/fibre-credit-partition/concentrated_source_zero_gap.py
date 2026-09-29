"""An actual divisor-closed noncover refuting a source-uniform eight-label gap.

Uses exact CRT residues, actual private integers, and the same source throughout.
It certifies neither global extremality nor a whole cover.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import gcd
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input', default='docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_actual_roots_input.json')
ap.add_argument('--output')
args = ap.parse_args()
raw = Path(args.input).read_bytes()
data = json.loads(raw)
primes = data['primes']
heights = dict(zip(primes, data['heights']))
roots = dict(data['selected_witness'])
star_roots = {(q,e): t for q,e,t in data['star_roots']}
checks = 0

def need(condition, msg):
    global checks
    checks += 1
    if not condition:
        raise ValueError(msg)

def valuation(n,p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e

def crt(spec):
    a,m = 0,1
    for mod,b in sorted(spec):
        a += m * (((b-a)*pow(m,-1,mod)) % mod)
        m *= mod
    return a,m

def intersection_mass(q,e,a,f,b):
    return F(1,q**max(e,f)) if (a-b) % (q**min(e,f)) == 0 else F(0)

family = []
def add(kind, coords, ternary=None, cofactor=None, epsilon=None):
    spec = [(q**e,a) for q,(e,a) in coords.items()]
    if ternary is not None:
        spec.append((3,ternary))
    a,m = crt(spec)
    family.append({'kind':kind,'modulus':m,'residue':a,'coords':coords,
                   'ternary':ternary,'cofactor':cofactor,'epsilon':epsilon})

add('pure3',{},0)
for q,h in heights.items():
    for e in range(1,h+1):
        add('pure',{q:(e,0 if e==1 else 1+q**(e-1))})
        t = star_roots[q,e]
        need(t == (1 if q==5 else 2),'Unchanged original star-root metadata')
        add('star',{q:(e,2 if e==1 else 1+2*q**(e-1))},t)
need(len(family)==85,'Same85 numerical pure/star originals')

selected = [455,665,805,1015,1085,1295,1435,5915]
cells = dict(zip(selected,[(3,2),(3,3),(3,4),(3,5),(3,6),(4,2),(4,3),(4,4)]))
mixed = set()
for d in selected:
    for k in range(2,d+1):
        if d % k == 0 and sum(k % q == 0 for q in primes)>=2:
            mixed.add(k)
need(len(mixed)==25,'Complete25 mixed-cofactor divisor closure')

def side(r,e,k):
    return k if e==1 else 1+k*r**(e-1)

for d in sorted(mixed):
    support = [q for q in primes if d % q == 0]
    for eps in (0,1):
        t = roots[d] if eps else None
        if d == 35:
            need(roots[d]==2,'Original105 root preserved')
            coords = {5:(1,1 if eps==0 else 3),7:(1,1 if eps==0 else 3)}
        else:
            outside = [r for r in support if r not in (5,7)]
            need(len(outside)==1 and outside[0]>=13,'One large cofactor prime')
            r = outside[0]
            e = valuation(d,r)
            if 5 in support and 7 not in support:
                k = 3+eps
                coords = {5:(1,3),r:(e,side(r,e,k))}
                need(roots[d]==1,'Actual5r root preserved')
            elif 7 in support and 5 not in support:
                k = 5+eps
                coords = {7:(1,3),r:(e,side(r,e,k))}
                need(roots[d]==2,'Actual7r root preserved')
            else:
                k = 7+eps
                a,b = cells[d] if eps else (3,3)
                coords = {5:(1,a),7:(1,b),r:(e,side(r,e,k))}
                need(roots[d]==1,'Actual target root preserved')
        add('mixed',coords,t,d,eps)

labels = {r['modulus'] for r in family}
need(len(family)==len(labels)==135,'135 distinct numerical originals')
need(all(m>1 and m%2==1 for m in labels),'Odd nonunit originals')
for row in family:
    m = row['modulus']
    # Enumerate numerical divisors by exact prime exponents, not a period scan.
    divisors = [1]
    for p in [3]+primes:
        e = valuation(m,p)
        divisors = [d*p**j for d in divisors for j in range(e+1)]
    for d in divisors:
        if d>1:need(d in labels,'Original numerical divisor closure')
for a,b in combinations(family,2):
    if a['modulus']%b['modulus']==0 or b['modulus']%a['modulus']==0:
        need((a['residue']-b['residue'])%gcd(a['modulus'],b['modulus'])!=0,
             'Comparable originals are disjoint')

# Full-period CRT private integers, checked literally against every original.
period = 3
for q,h in heights.items():period *= q**h
for row in family:
    values = {q:1 for q in primes}
    if row['kind'] in ('pure3','pure','star'):
        values[7] = 3
        if 7 in row['coords']:values[5] = 3
    values.update({q:a for q,(e,a) in row['coords'].items()})
    t = row['ternary'] if row['ternary'] is not None else 1
    witness,wperiod = crt([(3,t)]+[(q**heights[q],values[q]) for q in primes])
    need(wperiod==period,'One full original period')
    owners = [r['modulus'] for r in family if witness%r['modulus']==r['residue']]
    need(owners==[row['modulus']],'Actual integer is private for its original')
    row['private_integer'] = witness

uncovered,_ = crt([(3,1)]+[(q**heights[q],3 if q==7 else 1) for q in primes])
need(all(uncovered%r['modulus']!=r['residue'] for r in family),'Explicit integer proves this is a noncover')

# All actual JP1 tables, not merely the target bucket.
jp_tables = []
for p,q in combinations(primes,2):
    for t in (1,2):
        occupancy = {}
        for row in family:
            if row['modulus']%(3*p*q)==0 and row['ternary']==t:
                cell = (row['residue']%p,row['residue']%q)
                occupancy.setdefault(cell,[]).append(row['modulus'])
        need(all(len(v)<=2 for v in occupancy.values()),'All single-phase capacities')
        doubles = [k for k,v in occupancy.items() if len(v)==2]
        need(len({a for a,b in doubles})==len(doubles),'Double cells form a row matching')
        need(len({b for a,b in doubles})==len(doubles),'Double cells form a column matching')
        for (a,u),(b,v) in combinations(occupancy.items(),2):
            if a[0]==b[0] or a[1]==b[1]:
                need(len(u)+len(v)<=3,'Every actual JP1 row/column pair')
        if occupancy:
            jp_tables.append({'p':p,'q':q,'ternary_root':t,
                              'cells':[{'phase':list(k),'labels':v} for k,v in sorted(occupancy.items())]})
need(all(len(c['labels'])==1 for t in jp_tables for c in t['cells']),'All occupied pair cells are singly occupied')

# One exact source: same c and beta as FC36, with higher holes sharing root1.
caps = {}
betas = {}
source_matrix = {}
for q,h in heights.items():
    pure = [(e,0 if e==1 else 1+q**(e-1)) for e in range(1,h+1)]
    stars = [(e,2 if e==1 else 1+2*q**(e-1)) for e in range(1,h+1)]
    all_holes = pure+stars
    for (e,a),(f,b) in combinations(all_holes,2):
        need(intersection_mass(q,e,a,f,b)==0,'Complete pure/star chains disjoint in one coordinate')
    u = sum((F(1,q**e) for e in range(1,h+1)),F(0))
    c = 1/(1-u)
    need(c==F((q-1)*q**h,(q-2)*q**h+1),'Unchanged exact pure normalizer')
    caps[q] = c
    for t in (1,2):
        active = stars if t==(1 if q==5 else 2) else []
        beta = c*sum((F(1,q**e) for e,a in active),F(0))
        betas[q,t] = beta
        need(beta==(c-1 if active else 0),'Unchanged exact beta array')
        ratios = []
        for a in range(q):
            available = F(1,q)-sum((intersection_mass(q,1,a,e,b) for e,b in pure+active),F(0))
            ratios.append(q*available)
        need(sum(ratios,F(0))==q*(1-beta)/c,'Same-source total-mass row constraint')
        sorted_ratios = sorted(ratios,reverse=True)
        need(sum(0<v<1 for v in sorted_ratios)<=1,'Concentrated source row has at most one fractional entry')
        source_matrix[q,t] = ratios
need(source_matrix[5,1]==[0,F(313,625),0,1,1],'Two full5 roots after coalescing holes')
need(source_matrix[7,1]==[0,F(2001,2401),1,1,1,1,1],'Five full7 roots on target ternary root')

mass_rows = []
for d in selected:
    original = next(r for r in family if r['modulus']==3*d)
    exact,cap = F(1),F(1,d)
    for q in primes:
        h = heights[q]
        pure = [(e,0 if e==1 else 1+q**(e-1)) for e in range(1,h+1)]
        active = [(e,2 if e==1 else 1+2*q**(e-1)) for e in range(1,h+1)] if q==5 else []
        if q in original['coords']:
            e,a = original['coords'][q]
            available = F(1,q**e)-sum((intersection_mass(q,e,a,f,b) for f,b in pure+active),F(0))
            need(available==F(1,q**e),'Target own-coordinate cylinder avoids all pure and active-star holes')
            exact *= caps[q]*available
            cap *= caps[q]
        else:
            exact *= 1-betas[q,1]
    need(exact==cap,'Actual same-source target charge attains its independent cap')
    mass_rows.append({'cofactor':d,'modulus':3*d,'p5_p7_cell':list(cells[d]),'mass':str(exact)})
for a,b in combinations([r for r in family if r['modulus'] in {3*d for d in selected}],2):
    need((a['residue']-b['residue'])%gcd(a['modulus'],b['modulus'])!=0,'Target8 events pairwise disjoint')
need(len(set(cells.values()))==8,'Eight different full-cap cells')

result = {
 'contract':'135-class actual divisor-closed irredundant NONCOVER; same complete pure/star numerical chains, same beta and caps, all JP1 tables valid; no global-extremality assertion',
 'input':args.input,'input_sha256':sha256(raw).hexdigest(),
 'class_count':len(family),'full_period':period,'uncovered_integer':uncovered,
 'family':[{'kind':r['kind'],'modulus':r['modulus'],'residue':r['residue'],
            'private_integer':r['private_integer']} for r in sorted(family,key=lambda z:z['modulus'])],
 'mixed_cofactors':sorted(mixed),
 'source_root_ratios':{f'{q}:{t}':[str(v) for v in ratios] for (q,t),ratios in source_matrix.items()},
 'source_beta':{f'{q}:{t}':str(v) for (q,t),v in betas.items()},
 'target_mass_rows':mass_rows,'target_sum_cap':str(sum((F(r['mass']) for r in mass_rows),F(0))),
 'target_cap_deficit':'0','target_union_deficit':'0',
 'jp_pair_count':55,'jp_root_table_count':110,'jp_nonempty_tables':jp_tables,
 'checks':checks,
}
serialized = json.dumps(result,indent=2,sort_keys=True)+'\n'
if args.output:Path(args.output).write_text(serialized)
else:print(serialized,end='')
print(json.dumps({'checks':checks,'class_count':len(family),'target_cap_deficit':'0','target_union_deficit':'0','all_pair_cells_single':True,'input_sha256':result['input_sha256']},sort_keys=True))
