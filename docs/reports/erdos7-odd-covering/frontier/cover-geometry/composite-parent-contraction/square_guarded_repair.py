#!/usr/bin/env python3
"""Exact q=5,7 phase controls for the guarded q^2 parent repair.

Checks actual proper-original phases, full-period repaired sets, and support
counts. It does not enumerate covers or certify whole-cover minimality.
"""
import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def crt9(a,b,m):
    return (a+9*((b-a)*pow(9,-1,m)%m))%(9*m)


def check(q):
    h, period = 3*q*q, 9*q*q
    R,T = 2*q*(q-1)-2,4*q*q-6*q-3
    rows = {'prime':q,'joint_period':period,'proper_phase_assignments':0,
            'guarded_assignments':0,'unguarded_assignments':0,
            'allowed_original_h_phase_assignments':0,
            'guarded_full_liability_target_checks':0,
            'guarded_inventory_bound':R,'unguarded_inventory_bound':T-2,
            'uniform_inventory_bound':T-2,
            'repair_moduli':[9,9*q,9*q*q],
            'repair_modulus_sum':9*(1+q+q*q),'three_deleted_sum_lower_bound':9*h,
            'same_star_root_capacity_max':2*q*(q-2)-1,
            'different_star_roots_capacity_max':[2*q*(q-2),R-1]}
    require(9*(1+q+q*q)<9*h,'strict count-tie sum comparison')
    for old in range(q*q):
        if old%q==0:
            continue
        for root in (1,2):
            for u in range(1,q):
                delta=int(old%q==u)
                rows['proper_phase_assignments']+=1
                rows['guarded_assignments' if delta else 'unguarded_assignments']+=1
                allowed = [n for n in range(h) if n%3 and n%q and n%(q*q)!=old
                           and not(n%3==root and n%q==u)]
                counts = [sum(n%3==r for n in allowed) for r in (1,2)]
                for r,M in enumerate(counts,1):
                    expected=q*(q-1)-1-(q-delta)*int(r==root)
                    require(M==expected,'actual phase support count')
                require(len(allowed)==2*q*q-3*q-2+delta,'total phase count')
                for own_h_phase in allowed:
                    rows['allowed_original_h_phase_assignments']+=1
                    own_root=own_h_phase%3
                    caps=[2*M-int(r==own_root) for r,M in enumerate(counts,1)]
                    for r,cap in enumerate(caps,1):
                        exact=R-2*(q-delta)*int(r==root)-int(r==own_root)
                        safe=R-2*(q-1)*int(r==root)-int(r==own_root)
                        require(cap==exact and cap<=safe,'root-presence capacity identity')
                    require(sum(caps)==T-2+2*delta,'total own-singleton capacity')
                if not delta:
                    continue
                other=3-root
                repairs=[(9,other),(9*q,crt9(other+3,old%q,q)),
                         (9*q*q,crt9(other+6,old,q*q))]
                require(len({m for m,a in repairs})==3,'distinct fresh moduli')
                require(all(m%9==0 for m,a in repairs),'height-two freshness')
                retained={n for n in range(period) if n%3==0 or (n%3==root and n%q==u)}
                new_repairs={n for n in range(period) if any(n%m==a for m,a in repairs)}
                old_parent={n for n in range(period) if n%(q*q)==old}
                require(old_parent<=retained|new_repairs,'whole old-parent repair')
                active_projection={n%(q*q) for n in allowed}
                require(len(active_projection)==q*(q-1)-1,'vertical allowed support count')
                require(2*len(active_projection)==R,'vertical total capacity')
                for target in range(q*q):
                    new_parent={n for n in range(period) if n%(q*q)==target}
                    # The two complete target h-cells contain every deleted original
                    # at this projection, regardless of its other factors/heights.
                    deleted_superunion={n for n in new_parent if n%3}
                    old_union=retained|old_parent|deleted_superunion
                    new_union=retained|new_parent|new_repairs
                    require(old_union<=new_union,'whole liability including removed union')
                    rows['guarded_full_liability_target_checks']+=1
    require(rows['proper_phase_assignments']==2*q*(q-1)**2,'proper phase census')
    require(rows['guarded_assignments']==2*q*(q-1),'guarded phase census')
    require(R<T-2,'uniform branch domination')
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result={'scope':'Finite actual-phase and complete-period controls only; general all-height proof is separate.',
            'cases':[check(5),check(7)],'checks_passed':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
