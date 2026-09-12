#!/bin/bash
# clean-runlocal: remove run-local artifact directories/files under ROOT listed in a manifest.
# usage: clean-runlocal.sh --manifest <abs path to JSON {"paths":[...]}> [--root /tmp/ie0904] [--min-age-min 15] [--delete]
# Default is dry-run. Refuses: paths outside ROOT, ROOT itself, symlinks, paths younger than --min-age-min (recursively newest mtime), and anything in --keep (JSON list) .
set -u
manifest=""; root=/tmp/ie0904; delete=0; minage=15
while [ $# -gt 0 ]; do case "$1" in
  --manifest) manifest="$2"; shift 2;; --root) root="$2"; shift 2;; --delete) delete=1; shift;; --min-age-min) minage="$2"; shift 2;;
  *) echo "clean-runlocal: USAGE_ERROR: unknown option $1" >&2; exit 64;; esac; done
[ -n "$manifest" ] && [ -f "$manifest" ] || { echo "clean-runlocal: USAGE_ERROR: --manifest required" >&2; exit 64; }
case "$root" in /tmp/*|/private/tmp/*) ;; *) echo "clean-runlocal: USAGE_ERROR: root must be under /tmp" >&2; exit 64;; esac
python3 - "$manifest" "$root" "$delete" "$minage" <<'PY'
import json,os,sys,shutil,time
manifest,root,delete,minage=sys.argv[1],os.path.realpath(sys.argv[2]),sys.argv[3]=="1",float(sys.argv[4])
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
    if rp==root: rec["reason"]="is_root"
    elif not rp.startswith(root+os.sep): rec["reason"]="outside_root"
    elif not os.path.lexists(rp): rec["reason"]="missing"
    elif os.path.islink(rp): rec["reason"]="symlink"
    elif (now-newest(rp))<minage*60: rec["reason"]="too_recent"
    else: rec["eligible"]=True
    if rec["eligible"] and delete:
        try:
            shutil.rmtree(rp) if os.path.isdir(rp) else os.remove(rp); rec["state"]="removed"
        except Exception as e: rec["state"]="error"; rec["reason"]=str(e)
    out.append(rec)
print(json.dumps({"root":root,"delete":delete,"min_age_min":minage,"entries":out,"would_remove":[r["path"] for r in out if r["eligible"] and not delete],"removed":[r["path"] for r in out if r["state"]=="removed"]},indent=1))
sys.exit(0)
PY
