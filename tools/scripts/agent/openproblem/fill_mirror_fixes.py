#!/usr/bin/env python3
"""Fill <<MIRROR_FIXES>> in a Stage-B brief from a mirror-check result envelope.
usage: fill_mirror_fixes.py SCRATCHPAD LANE MIRROR_RESULT_JSON  → writes briefs/impl-op-w1-<lane>.stageB.filled.md and prints verdict"""
import sys,pathlib,json
sp=pathlib.Path(sys.argv[1]); lane=sys.argv[2]; res=json.load(open(sys.argv[3])); c=res.get('conclusion') or res
v=c.get('verdict'); bf=c.get('blocking_findings') or []; af=c.get('advisory_findings') or []
lines=[]
if v=='approve' and not bf:
    lines.append('(mirror check APPROVED — no fixes; do not touch the .lean/.scribe.cs; regenerate the .md only via `make emit`.)')
else:
    lines.append(f'Mirror check verdict: {v}. Apply EXACTLY these fixes to the Scribe source (and Lean only if a fix names it), then `make emit` and read the emitted .md value by value:')
    for i,f in enumerate(bf,1):
        if isinstance(f,dict): lines.append(f"{i}. [{f.get('file_line','')}] {f.get('claim','')} → FIX: {f.get('fix','')}")
        else: lines.append(f"{i}. {f}")
if af: lines.append('Advisory (fix if cheap): '+' | '.join(a if isinstance(a,str) else json.dumps(a,ensure_ascii=False) for a in af))
p=sp/'briefs'/f'impl-op-w1-{lane}.stageB.md'; t=p.read_text(); assert t.count('<<MIRROR_FIXES>>')==1
out=sp/'briefs'/f'impl-op-w1-{lane}.stageB.filled.md'; out.write_text(t.replace('<<MIRROR_FIXES>>','\n'.join(lines)))
print('verdict',v,'blocking',len(bf),'advisory',len(af),'->',out.name)
