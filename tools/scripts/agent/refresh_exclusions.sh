#!/bin/bash
# 器律⑨: in-flight exclusion set for lease cutting = receipts on origin/dev + receipts touched by any OPEN PR + atoms in every lease-*.json of LEASE_DIR.
# usage: refresh_exclusions.sh REPO LEASE_DIR OUT.txt   (sentinel: EXCLUSIONS_OK n=<count>)
set -euo pipefail
[ $# -eq 3 ] || { echo "EXCLUSIONS_USAGE: refresh_exclusions.sh REPO LEASE_DIR OUT.txt" >&2; exit 64; }
[ -d "$1/.git" ] || [ -f "$1/.git" ] || { echo "EXCLUSIONS_BAD_REPO=$1" >&2; exit 65; }
[ -d "$2" ] || { echo "EXCLUSIONS_BAD_LEASE_DIR=$2" >&2; exit 66; }
python3 -X utf8 - "$@" <<'PY'
import json, glob, subprocess, sys, os
repo, lease_dir, out = sys.argv[1:4]
ids=set(p.split('/')[-1].replace('.v1.json','') for p in subprocess.run(['git','-C',repo,'ls-tree','-r','--name-only','origin/dev','--','Meta/Digestion/formalizations/'],capture_output=True,text=True,check=True).stdout.split())
n_dev=len(ids)
prs=json.loads(subprocess.run(['env','-u','GH_TOKEN','-u','GITHUB_TOKEN','gh','pr','list','--repo','the-omega-institute/trureturing','--state','open','--limit','100','--json','number,files'],capture_output=True,text=True,check=True).stdout or '[]')
assert len(prs)<100, 'EXCLUSIONS_OPEN_PR_LIST_TRUNCATED'
n_pr=0
for pr in prs:
    for f in pr.get('files',[]):
        p=f['path']
        if p.startswith('Meta/Digestion/formalizations/'): ids.add(p.split('/')[-1].replace('.v1.json','')); n_pr+=1
n_lease=0
for f in glob.glob(os.path.join(lease_dir,'lease-*.json')):
    d=json.load(open(f,encoding='utf-8')); atoms=d.get('atoms',[]) if isinstance(d,dict) else d
    for a in atoms:
        aid=a['atom_id'] if isinstance(a,dict) else a
        if aid: ids.add(aid); n_lease+=1
open(out,'w',encoding='utf-8').write('\n'.join(sorted(ids))+'\n')
print(f'EXCLUSIONS_OK n={len(ids)} dev_receipts={n_dev} open_pr_receipts={n_pr} lease_atoms={n_lease}')
PY
