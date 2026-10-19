#!/usr/bin/env python3
"""Inspect obsolete per-module report caches; --delete removes only matching cache files."""
from common import entry
def main(argv):
    import sys, zipfile, json, os
    wt = argv[1]
    delete = '--delete' in argv
    d = os.path.join(wt, '.lake/build/lean-inspector/modules')
    stale = []
    scanned = 0
    for name in sorted(os.listdir(d)):
        if not name.endswith('.zip'):
            continue
        p = os.path.join(d, name)
        scanned += 1
        try:
            z = zipfile.ZipFile(p)
            raw = json.loads(z.read('raw-lean-report.json'))
        except Exception:
            continue
        bad = False
        for m in raw.get('modules', []):
            f = m.get('fib_analysis')
            if f is not None and (not isinstance(f, dict) or set(f) != {'applications'}):
                bad = True
        if bad:
            stale.append(p)
            if delete:
                for suffix in ('', '.trace', '.hash'):
                    try:
                        os.remove(p + suffix)
                    except FileNotFoundError:
                        pass
    print(f'PURGE_STALE_FIB scanned={scanned} stale={len(stale)} deleted={(len(stale) if delete else 0)}')
    for p in stale[:10]:
        print(' ', os.path.basename(p))

if __name__ == "__main__":
 import sys
 sys.exit(entry(main, minimum=1, maximum=2))
