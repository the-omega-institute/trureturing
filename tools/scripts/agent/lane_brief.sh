#!/bin/bash
# 器律⑨: deposit-lane brief renderer for the sshx formalization line (session w72 lineage).
# usage: lane_brief.sh LANE WORKTREE BASESHA LEASE.json EXCL.txt OUT.md HEAD_TEMPLATE.md BODY_TEMPLATE.md [PROBE_NOTE.txt]
#   LEASE.json = list (or {"atoms":[...]}) of digest-status candidate rows: source_id, atom_id, kind, atom_text
#   EXCL.txt   = one atom_id per line (see refresh_exclusions.sh)
# Glue, not program (CLAUDE.md 第 11 条辨析): fail-fast on inputs, sentinel line `LANE_BRIEF_OK` on success, idempotent (rewrites OUT).
# The two prompt templates are DATA supplied by the caller (owner ruling #4065: no data inside scripts); this file is program only.
set -euo pipefail
[ $# -ge 8 ] || { echo "LANE_BRIEF_USAGE: lane_brief.sh LANE WORKTREE BASESHA LEASE.json EXCL.txt OUT.md HEAD_TEMPLATE.md BODY_TEMPLATE.md [PROBE_NOTE]" >&2; exit 64; }
python3 -X utf8 - "$@" <<'PY'
import sys as _sys

import json,sys,subprocess,collections,os
lane,wt,base,leasef,exclf,out,headf,bodyf=sys.argv[1:9]
probe=open(sys.argv[9],encoding='utf-8').read() if len(sys.argv)>9 else ''
for p,what in ((headf,'HEAD_TEMPLATE'),(bodyf,'BODY_TEMPLATE')):
    assert os.path.isfile(p), f'LANE_BRIEF_MISSING_{what}={p}'
HEAD=open(headf,encoding='utf-8').read(); BODY=open(bodyf,encoding='utf-8').read()
for p,what in ((wt,'WORKTREE'),(leasef,'LEASE'),(exclf,'EXCL')):
    assert os.path.exists(p), f'LANE_BRIEF_MISSING_{what}={p}'
assert len(base)>=7 and all(c in '0123456789abcdef' for c in base), f'LANE_BRIEF_BAD_BASESHA={base}'
head=HEAD.replace('LANE',lane).replace('WORKTREE',wt).replace('BASESHA',base)
body=BODY.replace('LANE',lane).replace('BASESHA',base)
lease=json.load(open(leasef,encoding='utf-8')); lease=lease.get('atoms',lease) if isinstance(lease,dict) else lease
assert lease, 'LANE_BRIEF_EMPTY_LEASE'
parts=[head.rstrip('\n'),'']
for i,a in enumerate(lease,1):
    parts.append(f"{i}. atom_id: {a['atom_id']}\n   source: {a['source_id']}  kind: {a['kind']}\n   atom_text:\n---\n{a['atom_text']}\n---")
if probe: parts.append('\n>>> '+probe.strip()+'\n')
subprocess.run(['git','-C',wt,'fetch','-q','origin','dev'],check=True)
cnt=collections.Counter()
for path in subprocess.run(['git','-C',wt,'ls-tree','-r','--name-only','origin/dev','--','D5/'],capture_output=True,text=True,check=True).stdout.split():
    if path.endswith('.lean'): cnt[path.rsplit('/',1)[0]]+=1
openadd=collections.Counter()
try:
    prs=json.loads(subprocess.run(['env','-u','GH_TOKEN','-u','GITHUB_TOKEN','gh','pr','list','--state','open','--limit','100','--json','number,headRefName'],capture_output=True,text=True).stdout or '[]')
    assert len(prs)<100, 'LANE_BRIEF_OPEN_PR_LIST_TRUNCATED'
    for pr in prs:
        br=pr['headRefName']; subprocess.run(['git','-C',wt,'fetch','-q','origin',br],capture_output=True)
        added=subprocess.run(['git','-C',wt,'diff','--name-only','--diff-filter=A','origin/dev',f'origin/{br}','--','D5/'],capture_output=True,text=True).stdout.split()
        for path in added:
            if path.endswith('.lean'): openadd[path.rsplit('/',1)[0]]+=1
except Exception as e:
    openadd=collections.Counter(); print('open-PR census skipped:', e, file=sys.stderr)
for d,n in openadd.items(): cnt[d]+=n
full=sorted((d,n) for d,n in cnt.items() if n>=20 and d.startswith('D5/'))
parts.append('\nBUCKETS AT OR NEAR THE ADMISSION LIMIT ON origin/dev RIGHT NOW (limit 24; = origin/dev count PLUS modules added by currently OPEN PRs (they may land before you); computed at brief time - RE-CHECK against a fresh `git fetch origin dev && git ls-tree origin/dev --name-only <dir>/ | wc -l` immediately before `make deposit` AND again before push; your pinned tree is NOT the union): '+'; '.join(f'{d}={n}' for d,n in full)+' -- a new module must NOT go into any directory whose union count would exceed 24 after ALL of your additions; at 24 never add; at 20-23 add at most (24 - listed count) modules there and prefer the semantically matching sibling with room when in doubt.\n')
own={a['atom_id'] for a in lease}
excl=[l.strip() for l in open(exclf,encoding='utf-8') if l.strip() and l.strip() not in own]
parts.append('\nIn-flight exclusions (atoms other lanes hold or open PRs cover - do NOT take):\n\n'+'\n'.join(excl)+'\n')
parts.append(body)
txt='\n'.join(parts)
for a in lease: assert a['atom_text'] in txt and a['atom_id'] in txt, 'LANE_BRIEF_BYTE_FIDELITY'
for tok in ('LANE','WORKTREE','BASESHA'): assert tok not in txt, f'LANE_BRIEF_UNSUBSTITUTED_{tok}'
open(out,'w',encoding='utf-8').write(txt)
print(f'LANE_BRIEF_OK out={out} bytes={len(txt)} atoms={len(lease)} excl={len(excl)}')

PY
