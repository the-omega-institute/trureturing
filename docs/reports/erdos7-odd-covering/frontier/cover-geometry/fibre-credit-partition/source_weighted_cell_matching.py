"""Independent exact control for the FC36 source-attached 5/7 matching gap.

This verifies a fixed source/inventory upper relaxation, not a whole cover.
Run from the repository root, or pass --input with an explicit fixture path.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input', default='docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_actual_roots_input.json')
parser.add_argument('--output')
args = parser.parse_args()
raw = Path(args.input).read_bytes()
x = json.loads(raw)
checks = 0

def need(condition, reason):
    global checks
    checks += 1
    if not condition:
        raise ValueError(reason)

def frac(v):
    return str(F(v))

heights = dict(zip(x['primes'], x['heights']))
need(heights[5] == heights[7] == 5, 'Specified source heights')
c = {q: F((q-1)*q**h, (q-2)*q**h+1) for q,h in heights.items()}
star = {(q,e): t for q,e,t in x['star_roots']}
for q,h in heights.items():
    for e in range(1,h+1):
        need(star[q,e] == (1 if q == 5 else 2), 'One complete actual star assignment')

# Construct the actual pure-survivor and star residual counts, independently
# of the quotient formulas used in the mathematical proof.
source_rows = {}
for q in (5,7):
    h = heights[q]
    period = q**h
    pure = [(q,0)] + [(q**e,1+q**(e-1)) for e in range(2,h+1)]
    active_stars = [(q**e,2 if e == 1 else 3+q**(e-1))
                    for e in range(1,h+1) if star[q,e] == 1]
    count = [0]*q
    pure_count = 0
    for a in range(period):
        if any(a % m == b for m,b in pure):
            continue
        pure_count += 1
        if not any(a % m == b for m,b in active_stars):
            count[a % q] += 1
    need(F(period,pure_count) == c[q], 'Actual same-source normalization')
    ratios = [F(n,pure_count)/(c[q]/q) for n in count]
    source_rows[q] = {'period':period,'pure_survivor_count':pure_count,
                      'residual_first_root_counts':count,'ratios':ratios}
rho5 = F(469,625)
rho7 = F(2001,2401)
need(source_rows[5]['ratios'] == [0,rho5,0,rho5,1], 'Five-coordinate source matrix')
need(source_rows[7]['ratios'] == [0,rho7,1,1,1,1,1], 'Seven-coordinate source matrix')
need(0 < rho5 < rho7 < 1, 'Strict slot hierarchy')

labels = [d for d,t in x['selected_witness']
          if t == 1 and d % 35 == 0 and d % 25 != 0 and d % 49 != 0]
need(sorted(labels) == [455,665,805,1015,1085,1295,1435,5915], 'Exact original shallow bucket')
def coefficient(d):
    ans = F(1,d)
    for q in heights:
        if d % q == 0:
            ans *= c[q]
    return ans
weighted = sorted(((d,coefficient(d)) for d in labels), key=lambda z:z[1], reverse=True)
need([d for d,_ in weighted] == labels, 'Exact decreasing numerical coefficients')
need(weighted[-2][0] == 1435 and weighted[-1][0] == 5915, 'Two smallest actual coefficients')
base = sum((a for _,a in weighted), F(0))
loss = (1-rho7)*weighted[-2][1] + (1-rho5)*weighted[-1][1]
need(loss == F(635674842953,2406595308643068), 'Exact strict necessary debit deficit')
need(loss > 0, 'Positive fixed-source gain')

rows = (1,3,4)
cols = tuple(range(1,7))
cell = {(r,s): source_rows[5]['ratios'][r]*source_rows[7]['ratios'][s]
        for r in rows for s in cols}
majorant = [F(1)]*6+[rho7,rho5]
maximum = F(-1)
winner = None
matchings = 0
for k in range(4):
    for selected_rows in combinations(rows,k):
        for selected_cols in combinations(cols,k):
            for perm in permutations(selected_cols):
                matching = tuple(zip(selected_rows,perm))
                slots = sorted(list(cell.values())+[cell[e] for e in matching],reverse=True)[:8]
                need(all(a <= b for a,b in zip(slots,majorant)), 'All matching slot lists obey the analytical majorant')
                score = sum((a*v for (_,a),v in zip(weighted,slots)),F(0))
                if score > maximum:
                    maximum,winner = score,matching
                matchings += 1
need(matchings == 229, 'All partial matchings enumerated')
need(maximum == base-loss, 'Weighted relaxation bound is exact')
# Excluding one globally fixed old35 phase (1,1) does not alter the top8
# attainable slots of the displayed matching. This is not a separate old
# phase per label or ternary root.
fixed_matching = ((4,2),)
slots_after_old35 = sorted([v for e,v in cell.items() if e != (1,1)]
                          +[cell[e] for e in fixed_matching],reverse=True)[:8]
need(slots_after_old35 == majorant, 'One shared old35 phase remains excluded')

result = {
 'contract':'Conditional fixed FC36 85-original source plus global-extremal JP phase capacity; no whole-cover or uniform-all-sources assertion',
 'input':args.input,'input_sha256':sha256(raw).hexdigest(),
 'source_rows':{str(q): {k:([frac(a) for a in v] if k=='ratios' else v)
                         for k,v in row.items()} for q,row in source_rows.items()},
 'root':1,'exact_valuations':{'5':1,'7':1},
 'coefficients':[{'cofactor':d,'original_modulus':3*d,'u':frac(a)} for d,a in weighted],
 'slot_majorant':[frac(a) for a in majorant],
 'base_independent_charge':frac(base),'necessary_deficit':frac(loss),
 'maximum_matching_relaxation_charge':frac(maximum),
 'matching_count':matchings,'relaxed_equality_matching':winner,
 'fixed_shared_old35_phase':[1,1],
 'root_weight_factor':'Multiply all charge values by the same original lambda3(root1)=w',
 'checks':checks,
}
serialized = json.dumps(result,indent=2,sort_keys=True)+'\n'
if args.output:
    Path(args.output).write_text(serialized)
else:
    print(serialized,end='')
print(json.dumps({'checks':checks,'matchings':matchings,'deficit':frac(loss),'approx_deficit':float(loss),'input_sha256':result['input_sha256']},sort_keys=True))
