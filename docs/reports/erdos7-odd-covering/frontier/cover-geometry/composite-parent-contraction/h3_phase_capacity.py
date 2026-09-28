"""Fixed105 phase and matching capacities with fresh repairs; no palette search."""
from itertools import product,combinations
from collections import Counter
from pathlib import Path
import argparse,json

def demand(test,message):
    if not test:raise ValueError(message)
def maximum_matching(cells):
    # Process the four p-roots; the bit mask remembers used q-roots.
    states={0:()}
    for u in range(1,5):
        following=dict(states)
        for mask,edges in states.items():
            for v in range(1,7):
                bit=1<<(v-1)
                if (u,v) in cells and not mask&bit:
                    following[mask|bit]=edges+((u,v),)
        states=following
    return max(states.values(),key=len)

rows=[];profiles=Counter();joint_rows=[]
for r15,q15,r21,q21,q35,r35 in product((1,2),range(1,5),(1,2),range(1,7),range(1,5),range(1,7)):
    live=[x for x in range(105) if x%3 and x%5 and x%7
          and not(x%3==r15 and x%5==q15)
          and not(x%3==r21 and x%7==q21)
          and not(x%5==q35 and x%7==r35)]
    counts=tuple(sum(x%3==r for x in live) for r in (1,2))
    demand(sum(counts)<=38 and max(counts)<=23,'analytic proper-divisor phase bounds')
    profiles[counts]+=1
    rows.append((counts,(r15,q15,r21,q21,q35,r35)))
    cells=tuple({(x%5,x%7) for x in live if x%3==r} for r in (1,2))
    matches=tuple(maximum_matching(table) for table in cells)
    sizes=tuple(map(len,matches))
    demand(sum(sizes)<=7 and max(sizes)<=4,'simultaneous matching bounds')
    demand(sizes[r15-1]<=3,'original15 removes one entire p-row')
    totals=tuple(n+k for n,k in zip(counts,sizes))
    demand(sum(totals)<=45 and max(totals)<=27,'joint phase-plus-matching bounds')
    # Reserve an allowed unmatched cell for original105's singleton phase.
    # This witnesses only the finite occupancy relaxation, not a whole cover.
    unmatched=[(r,u,v) for r in (1,2) for u,v in sorted(cells[r-1])
               if (u,v) not in matches[r-1]]
    demand(bool(unmatched),'an original105 singleton can avoid double-occupied cells')
    joint_rows.append(dict(phases=(r15,q15,r21,q21,q35,r35),allowed=counts,
        matching_sizes=sizes,matching_edges=matches,occupancy_upper=totals,
        original105_singleton_phase=unmatched[0]))
demand(len(rows)==2304,'all six-label phase assignments')
demand(max(sum(row[0]) for row in rows)==38,'attained proper-phase maximum')
demand(max(max(row[0]) for row in rows)==23,'attained individual-root phase maximum')
demand(max(sum(row['occupancy_upper']) for row in joint_rows)==45,'attained joint occupancy comparison')
demand(max(max(row['occupancy_upper']) for row in joint_rows)==27,'attained root occupancy comparison')

# Three fresh labels cover any target c mod105. All are absent if H3=1.
repair_labels=(9,45,63)
for c in range(105):
    roots=tuple(r for r in range(9) if r%3==c%3)
    residues=[]
    for modulus,root in zip(repair_labels,roots):
        cofactor=modulus//9
        residue=next(a for a in range(modulus) if a%9==root and a%cofactor==c%cofactor)
        residues.append(residue)
    demand(all(any(x%modulus==a for modulus,a in zip(repair_labels,residues))
               for x in range(c,315,105)),'fresh repair covers complete target on joint period315')
demand(sum(repair_labels)==117<3*105,'strict sum descent even without using distinctness')

def crt(pairs):
    value=0;period=1
    for modulus,residue in pairs:
        value+=next(k for k in range(modulus) if (value+period*k)%modulus==residue)*period
        period*=modulus
    return value,period

# Two cells sharing one nonternary coordinate use the same four fresh labels.
# Check all ternary/p/q roots, including zero roots, on the complete joint315.
joint_repair_cases=Counter()
for axis,other in ((5,7),(7,5)):
    for root,u,pair in product(range(3),range(axis),combinations(range(other),2)):
        v,w=pair
        classes=[crt([(9,root)]),crt([(9,root+3),(axis,u)]),
                 crt([(9,root+6),(other,v)]),
                 crt([(9,root+6),(axis,u),(other,w)])]
        demand({m for _,m in classes}=={9,45,63,315},'four distinct fresh labels')
        target=[x for x in range(315) if x%3==root and x%axis==u and x%other in pair]
        demand(len(target)==6,'two full105 phases have six points modulo315')
        demand(all(any(x%m==a for a,m in classes) for x in target),'shared four-label repair')
        joint_repair_cases[str(axis)]+=1
demand(dict(joint_repair_cases)=={'5':315,'7':210},'all525 same-row or same-column pairs')
demand(9+45+63+315==432<16*105,'four-class strict modulus-sum descent')

packet=[]
for large in (13,17,19):
    support=(5,7,11,large)
    residue,modulus=crt([(3,1)]+[(q,min(7,q-2)) for q in support])
    demand(residue%105==103,'literal comb classes have one phase')
    packet.append(dict(modulus=modulus,residue=residue,phase105=residue%105))
payload=dict(scope='Pure prime phases translated to0 once. All2304 actual choices of original15/21/35 phases outside their pure divisors. No whole-cover enumeration or Lean verification.',
    cases=len(rows),phase_profile_counts={','.join(map(str,k)):v for k,v in sorted(profiles.items())},
    maximum_allowed105_phases=38,maximum_allowed_phases_per_root=23,
    independent_phase_multiple105_upper=75,independent_phase_multiple105_per_root_upper=46,
    strengthened_multiple105_count=45,strengthened_uniform_multiple105_count_per_root=27,
    maximum_double_cells_total=7,maximum_double_cells_per_root=4,
    joint_phase_matching_extremum=next(row for row in joint_rows if sum(row['occupancy_upper'])==45),
    extrema=[dict(counts=counts,phases=phases) for counts,phases in rows if sum(counts)==38][:1],
    repair=dict(labels=repair_labels,sum=117,joint_period=315,target_phases_checked=105),
    shared_two_phase_repair=dict(labels=(9,45,63,315),sum=432,joint_period=315,
        cases_by_shared_prime=dict(joint_repair_cases),two_phase_pairs_checked=525),
    literal_noncover_comb_overfull_packet=packet,
    premises='One globally number-then-modulus-sum-minimal whole distinct odd cover, H3=1, divisor closure, comparable disjointness. Presence of any105 multiple forces all seven nonunit divisors including105. Each surviving phase has at most2 multiples; the original105 phase has exactly1. The shared four-label repair forces at most3 occupants in any two cells on one row or column of one ternary root, so double-occupied cells form a matching. The old75/46 independent-phase bounds are retained;45/27 are the stronger joint constraints. Finite occupancy extrema are not whole-cover constructions.')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,help='write the exact result to this explicit path')
args=parser.parse_args()
rendered=json.dumps(payload,indent=2)+'\n'
if args.output:args.output.write_text(rendered)
print(rendered,end='')
