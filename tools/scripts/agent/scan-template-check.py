#!/usr/bin/env python3
"""Reject a scan result whose rows are a filled-in template.
A seat can return COMPLETE with every schema field populated and zero information:
2026-09-16 W260 returned 103 content candidates whose witness, lean_statement and
dominator_check were byte-for-byte identical.  The tell is repeated strings across rows.
usage: scan-template-check.py <result.json>     exit 1 if any field looks templated
       scan-template-check.py --selftest           run the pinned positive/negative cases
"""
import json,sys,collections

FIELDS=(("settle_rows",("justification",)),
        ("content_candidates",("witness","lean_statement","dominator_check")),
        ("cover_rows",("clause_text",)))

def flagged(c):
    """-> list of (key, field, rows, distinct, most_common_count, text)"""
    out=[]
    for key,fields in FIELDS:
        rows=c.get(key,[]) or []
        for f in fields:
            vals=[str(r.get(f,"")) for r in rows if r.get(f) is not None]
            if len(vals)<3: continue
            n,u=len(vals),len(set(vals))
            top=collections.Counter(vals).most_common(1)[0]
            if u<=max(1,n//4) or top[1]>=max(3,n//2):
                out.append((key,f,n,u,top[1],top[0]))
    return out

def rows(field,texts): return [{field:x} for x in texts]

if "--selftest" in sys.argv[1:]:
    CASES=[
      # (name, conclusion, expected number of flagged fields)
      ("positive: one sentence repeated 10x",
       {"settle_rows": rows("justification",["same"]*10)}, 1),
      ("positive: 103 identical candidates (the 2026-09-16 case)",
       {"content_candidates":[{"witness":"w","lean_statement":"s","dominator_check":"d"}]*103}, 3),
      ("negative: every row distinct",
       {"settle_rows": rows("justification",[f"reason {i}" for i in range(20)])}, 0),
      ("negative: a few legitimate repeats of one shared reason",
       {"settle_rows": rows("justification",[f"reason {i}" for i in range(16)]+["shared"]*3)}, 0),
      ("negative: below the three-row floor",
       {"cover_rows": rows("clause_text",["same","same"])}, 0),
      # the threshold is most_common >= max(3, n//2): three of eight is below it, four of eight is at it
      ("negative: three of eight repeated is below the threshold",
       {"settle_rows": rows("justification",["same"]*3+[f"r{i}" for i in range(5)])}, 0),
      ("positive: four of eight repeated is at the threshold",
       {"settle_rows": rows("justification",["same"]*4+[f"r{i}" for i in range(4)])}, 1),
    ]
    bad=0
    for name,c,exp in CASES:
        got=len(flagged(c)); ok=(got==exp); bad+=0 if ok else 1
        print(f"  {'ok  ' if ok else 'FAIL'} {name:56s} expected={exp} got={got}")
    print(f"SELFTEST_{'PASS' if not bad else 'FAIL'} cases={len(CASES)} failed={bad}")
    sys.exit(1 if bad else 0)

c=json.load(open(sys.argv[1])).get("conclusion",{})
hits=flagged(c)
for key,fields in FIELDS:
    rws=c.get(key,[]) or []
    for f in fields:
        vals=[str(r.get(f,"")) for r in rws if r.get(f) is not None]
        if len(vals)<3: continue
        n,u=len(vals),len(set(vals))
        top=collections.Counter(vals).most_common(1)[0]
        flag=any(h[0]==key and h[1]==f for h in hits)
        print(f"{key}.{f}: rows={n} distinct={u} most_common_count={top[1]}" + ("   TEMPLATE" if flag else ""))
        if flag: print("   repeated text:",repr(top[0][:120]))
print(f"SCAN_TEMPLATE_CHECK templated_fields={len(hits)}")
sys.exit(1 if hits else 0)
