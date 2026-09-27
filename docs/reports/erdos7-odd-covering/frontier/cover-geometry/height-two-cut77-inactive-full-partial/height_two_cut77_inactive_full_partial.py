"""Exact necessary inventory excluding partial children at one inactive full root.
The checks are integer budget checks, not enumeration of actual sources or Lean.
"""
from argparse import ArgumentParser
from itertools import combinations,combinations_with_replacement
from pathlib import Path
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def records(n,q):
    answer=[]
    for delta in range(n-q+1):
        for costs in combinations_with_replacement(range(4),n-delta):
            contribution=7*delta+2*sum(costs)
            if contribution<=20:
                answer.append((delta,costs,contribution,sum(costs[:q])))
    return answer


def lower_records(q):
    answer=[]
    for delta in range(3):
        for p in range(3*q+1):
            value=7*delta+2*p+2*(2-delta)*((p+q-1)//q)
            if value<=20:answer.append((delta,p,value))
    return answer


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    full=records(5,3)
    gap=records(4,2)
    require((len(full),len(gap))==(72,55),'complete root-record counts')
    partial={}
    all_active={}
    full_lower=lower_records(3)
    gap_lower=lower_records(2)
    lower_min={}
    lower_survivors={}
    for k in range(9):
        partial_rows=[]
        active_rows=[]
        for f1,f2 in combinations_with_replacement(full,2):
            for g in gap:
                rows=(f1,f2,g)
                # Deliberately allow zero cost even at k0: the exclusion is stronger
                # than requiring every occupied child's original fibre nonempty.
                if 7*k+sum(r[2] for r in rows)!=56:continue
                if any(a[3]+b[3]<9-k for a,b in combinations(rows,2)):continue
                record=[dict(delta=r[0],costs=list(r[1]),contribution=r[2],least=r[3]) for r in rows]
                (partial_rows if any(r[0] for r in rows) else active_rows).append(record)
        partial[k]=partial_rows
        all_active[k]=active_rows
        require(not partial_rows,'no partial-child exact77 inventory at public cost '+str(k))
        valid=[]
        for a,b in combinations_with_replacement(full_lower,2):
            for c in gap_lower:
                rows=(a,b,c)
                if not any(r[0] for r in rows):continue
                if any(x[1]+y[1]<9-k for x,y in combinations(rows,2)):continue
                valid.append(rows)
        lower_min[k]=min(sum(r[2] for r in rows) for rows in valid)
        lower_survivors[k]=[rows for rows in valid if sum(r[2] for r in rows)<=56-7*k]
    require(list(lower_min.values())==[55,51,45,37,33,29,25,21,17],'rounded partial-budget table')
    require(lower_survivors[0]==[((0,5,18),(0,5,18),(1,4,19))],'unique k0 near-equality')
    require(all(not v for k,v in lower_survivors.items() if k>0),'positive-public exclusion')
    require(sum(row[0] for row in lower_survivors[0][0])%2==1 and 56%2==0,'k0 exact parity exclusion')
    result=dict(result='PASS',root_records=dict(full=len(full),gap=len(gap)),
                partial_inventory=partial,partial_lower_minimum=lower_min,
                partial_lower_survivors=lower_survivors,
                all_active_count_by_public={k:len(v) for k,v in all_active.items()},
                scope='Exhaustive necessary integer cut-budget inventory only; actual-source implication in accompanying proof; not Lean.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
