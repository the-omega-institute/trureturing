#!/usr/bin/env python3
"""Generate portable open-problem briefs. See README.md for modes and inputs."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "briefgen"))
from common import Context, entry
def legacy(argv):
    ctx = Context(argv[1])
    import sys, pathlib, json
    sp = pathlib.Path(argv[1])
    lane = argv[2]
    res = json.load(open(argv[3]))
    c = res.get('conclusion') or res
    v = c.get('verdict')
    bf = c.get('blocking_findings') or []
    af = c.get('advisory_findings') or []
    lines = []
    if v == 'approve' and (not bf):
        lines.append('(mirror check APPROVED — no fixes; do not touch the .lean/.scribe.cs; regenerate the .md only via `make emit`.)')
    else:
        lines.append(f'Mirror check verdict: {v}. Apply EXACTLY these fixes to the Scribe source (and Lean only if a fix names it), then `make emit` and read the emitted .md value by value:')
        for i, f in enumerate(bf, 1):
            if isinstance(f, dict):
                lines.append(f"{i}. [{f.get('file_line', '')}] {f.get('claim', '')} → FIX: {f.get('fix', '')}")
            else:
                lines.append(f'{i}. {f}')
    if af:
        lines.append('Advisory (fix if cheap): ' + ' | '.join((a if isinstance(a, str) else json.dumps(a, ensure_ascii=False) for a in af)))
    p = sp / 'briefs' / f'impl-op-w1-{lane}.stageB.md'
    t = p.read_text()
    assert t.count('<<MIRROR_FIXES>>') == 1
    out = sp / 'briefs' / f'impl-op-w1-{lane}.stageB.filled.md'
    out.write_text(t.replace('<<MIRROR_FIXES>>', '\n'.join(lines)))
    print('verdict', v, 'blocking', len(bf), 'advisory', len(af), '->', out.name)

def main(argv):

    if argv[1:2] == ['--prepare']:
        import subprocess
        if len(argv) != 5:
            from common import fail
            fail(10, '--prepare LANE NYXID_SEAT MIRROR_FLIGHT')
        return subprocess.call(['/bin/bash', str(Path(__file__).resolve().parent / 'briefgen/stageb_prep.sh'), *argv[2:]])
    return entry(legacy, argv, minimum=3, maximum=3)

if __name__ == "__main__":
    sys.exit(entry(main))
