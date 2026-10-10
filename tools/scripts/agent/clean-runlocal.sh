#!/bin/bash
# clean-runlocal: qualify manifest-listed temporary trees through the worktree protocol.
# usage: clean-runlocal.sh --manifest FILE [--root /tmp/ie0904] [--source REPO] [--base REV] [--min-age-min 15] [--delete]
# Default is preview. Registered trees use lock/time removal; other artifacts retain their policy.
set -u
protocol_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
manifest=""; root=/tmp/ie0904; delete=0; minage=15; source="$protocol_root"; base=origin/dev
while [ $# -gt 0 ]; do case "$1" in
  --manifest) manifest="$2"; shift 2;; --root) root="$2"; shift 2;; --delete) delete=1; shift;; --min-age-min) minage="$2"; shift 2;;
  --source) source="$2"; shift 2;; --base) base="$2"; shift 2;;
  *) echo "clean-runlocal: USAGE_ERROR: unknown option $1" >&2; exit 64;; esac; done
[ -n "$manifest" ] && [ -f "$manifest" ] || { echo "clean-runlocal: USAGE_ERROR: --manifest required" >&2; exit 64; }
case "$root" in /tmp|/private/tmp|/tmp/*|/private/tmp/*) ;; *) echo "clean-runlocal: USAGE_ERROR: root must be /tmp or under it" >&2; exit 64;; esac
python3 - "$manifest" "$root" "$delete" "$minage" "$source" "$base" "$protocol_root" <<'PY'
import argparse,json,os,sys,shutil,time
from pathlib import Path
manifest,root,delete,minage=sys.argv[1],os.path.realpath(sys.argv[2]),sys.argv[3]=="1",float(sys.argv[4])
source,base=Path(sys.argv[5]),sys.argv[6]
sys.path.insert(0,str(Path(sys.argv[7])/"tools/scripts/worktree"))
from worktree_protocol import inventory,Refused
from worktree_preservation import remove
paths=json.load(open(manifest)).get("paths",[]); now=time.time(); out=[]
def newest(p):
    m=os.lstat(p).st_mtime
    if os.path.isdir(p) and not os.path.islink(p):
        for d,ds,fs in os.walk(p):
            for n in ds+fs:
                try: m=max(m,os.lstat(os.path.join(d,n)).st_mtime)
                except FileNotFoundError: pass
    return m
for p in paths:
    rp=os.path.realpath(p); rec={"path":p,"eligible":False,"reason":None,"state":"kept"}
    if os.path.islink(p): rec["reason"]="symlink"
    elif rp==root: rec["reason"]="is_root"
    elif not rp.startswith(root+os.sep): rec["reason"]="outside_root"
    elif not os.path.lexists(rp): rec["reason"]="missing"
    elif (now-newest(rp))<minage*60: rec["reason"]="too_recent"
    else:
        try:
            trees=[Path(row["worktree"]).resolve() for row in inventory(source)]
            if any(Path(rp) in tree.parents for tree in trees): raise Refused("nested_worktree")
            registered=Path(rp) in trees
            if registered:
                result=remove(argparse.Namespace(source=source,names="",path=[Path(rp)],force=False,
                    preview=not delete,expected=[]))
                outcome=result["items"][0]["outcome"]
                if outcome=="partial_or_indeterminate": raise OSError(str(result))
            elif delete:
                shutil.rmtree(rp) if os.path.isdir(rp) else os.remove(rp)
            rec["eligible"]=True
            if delete: rec["state"]="removed"
        except Refused as e: rec["reason"]=str(e)
        except Exception as e: rec["state"]="error"; rec["reason"]=str(e)
    out.append(rec)
print(json.dumps({"root":root,"delete":delete,"min_age_min":minage,"entries":out,"would_remove":[r["path"] for r in out if r["eligible"] and not delete],"removed":[r["path"] for r in out if r["state"]=="removed"]},indent=1))
sys.exit(74 if any(r["state"]=="error" for r in out) else 0)
PY
