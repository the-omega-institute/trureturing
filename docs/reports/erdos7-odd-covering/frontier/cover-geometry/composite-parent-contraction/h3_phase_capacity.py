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

# Actual retained mixed originals permit a moved35 parent with full old liability.
# All proper-phase tables are inherited from the existing complete2304 list.
cross_cases=Counter();cross_extrema={};cross_maxima={};redundant_pq=0
moved_repair_checks=0
for row in joint_rows:
    r15,u,r21,v,x0,y0=row['phases']
    ep,eq=x0==u,y0==v
    same=r15==r21
    if not same and ep and eq:
        redundant_pq+=1
        demand(all(x%3==0 or(x%3==r15 and x%5==u) or
                   (x%3==r21 and x%7==v)
                   for x in range(105) if x%5==x0 and x%7==y0),
               'both guards cover the entire original35 class')
        continue
    guarded=ep or eq
    case=('same' if same else 'different')+('_guarded' if guarded else '_unguarded')
    cross_cases[case]+=1
    cells=tuple({(a,b) for a in range(1,5) for b in range(1,7)
        if not(r==r15 and a==u) and not(r==r21 and b==v)
        and(a,b)!=(x0,y0)} for r in(1,2))
    phase_count=sum(map(len,cells))
    expected=38-int(not guarded) if same else 36+int(guarded)
    demand(phase_count==expected,'exact proper-divisor count with guard status')
    if guarded:
        single=tuple(cells[i]-cells[1-i] for i in(0,1))
        doubles=tuple(maximum_matching(table) for table in single)
        demand(sum(map(len,doubles))<=2,'single-only cross or strip matching capacity')
        ceiling=phase_count+sum(map(len,doubles))
        guarded_root=r15 if ep else r21
        repair_root=3-guarded_root
        fresh=[crt([(9,repair_root)]),crt([(9,repair_root+3),(5,x0)]),
               crt([(9,repair_root+6),(7,y0)])]
        demand({m for _,m in fresh}=={9,45,63},'fresh mixed-guard repair labels')
        def retained_or_fresh(x):
            return(x%3==0 or(x%3==r15 and x%5==u) or
                   (x%3==r21 and x%7==v) or any(x%m==a for a,m in fresh))
        old=[x for x in range(315) if x%5==x0 and x%7==y0]
        demand(all(retained_or_fresh(x) for x in old),'full old35 liability is repaired')
        for a,b in product(range(1,5),range(1,7)):
            moved=crt([(5,a),(7,b)])
            target=[x for x in range(315) if x%3 and x%5==a and x%7==b]
            demand(len(target)==6,'two actual105 roots with three lifts each modulo315')
            demand(all(x%moved[1]==moved[0] or retained_or_fresh(x)
                       for x in set(old+target)),'same replacement covers all old and target liability')
            moved_repair_checks+=1
    else:
        doubles=tuple(maximum_matching(table) for table in cells)
        ceiling=phase_count+sum(map(len,doubles))
    universal={'same_unguarded':44,'different_unguarded':43,
               'same_guarded':40,'different_guarded':39}[case]
    demand(ceiling<=universal,'case-specific inventory bound')
    # A baseline single per allowed cell plus these doubles realizes this
    # relaxation; guarded doubles occur only where the opposite root is absent.
    occupancy={(r,a,b):1+int((a,b) in doubles[r-1])
               for r in(1,2) for a,b in cells[r-1]}
    if guarded:
        demand(all(sum(occupancy.get((r,a,b),0) for r in(1,2))<=2
                   for a,b in product(range(1,5),range(1,7))),
               'cross-root capacity in the attained comparison')
    singleton=next((key for key,value in sorted(occupancy.items()) if value==1),None)
    demand(singleton is not None,'original105 can occupy a single cell')
    if ceiling>cross_maxima.get(case,-1):
        cross_maxima[case]=ceiling
        cross_extrema[case]=dict(phases=row['phases'],allowed=tuple(map(len,cells)),
            double_cells=doubles,inventory_ceiling=ceiling,original105_singleton=singleton)
demand(redundant_pq==48 and sum(cross_cases.values())==2256,'actual nonredundant proper-phase cases')
demand(cross_maxima=={'same_unguarded':44,'different_unguarded':43,
                     'same_guarded':40,'different_guarded':39},'attained four case ceilings')
demand(moved_repair_checks==19584,'all guarded original/target phase pairs')

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
    retained_mixed_repair=dict(uniform_multiple105_count=44,
        cases=dict(sorted(cross_cases.items())),redundant_original35_cases=redundant_pq,
        case_maxima=cross_maxima,comparison_extrema=cross_extrema,
        fresh_labels=(9,45,63),joint_period=315,original_target_pairs_checked=moved_repair_checks),
    literal_noncover_comb_overfull_packet=packet,
    premises='One globally number-then-modulus-sum-minimal whole distinct odd cover, H3=1, divisor closure, comparable disjointness. Presence of any105 multiple forces all seven nonunit divisors including105. Each surviving phase has at most2 multiples; the original105 phase has exactly1. The shared four-label repair forces at most3 occupants in any two cells on one row or column of one ternary root, so double-occupied cells form a matching. The old75/46 independent-phase bounds are retained;45/27 are the stronger joint constraints. The retained mixed repair further gives44 total, or43/40/39 under the actual phase cases; it rules out48 redundant original35 phase choices. The earlier45 and root27 bounds remain valid. Finite occupancy extrema are not whole-cover constructions.')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,help='write the exact result to this explicit path')
args=parser.parse_args()
rendered=json.dumps(payload,indent=2)+'\n'
if args.output:args.output.write_text(rendered)
print(rendered,end='')
