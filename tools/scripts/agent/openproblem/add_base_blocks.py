#!/usr/bin/env python3
"""Generate portable open-problem briefs. See README.md for modes and inputs."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "briefgen"))
from common import Context, entry, fail
def legacy(argv):
    ctx = Context()
    import sys, pathlib, re
    source = pathlib.Path(__file__).resolve().parent / 'templates/impl-base-brief.md'
    if argv[1:2] == ['--base']:
        if len(argv) < 4:
            fail(10, '--base SOURCE requires at least one output file')
        source = pathlib.Path(argv[2])
        argv = [argv[0], *argv[3:]]
    base = source.read_text()
    blocks = []
    for key in ['**Public surface is deliberate.**', '**Imports are minimal', '**Provenance is typed']:
        i = base.find(key)
        assert i >= 0, key
        j = base.find('\n\n', i)
        blocks.append(base[i:j + 2])
    for f in argv[1:]:
        p = pathlib.Path(f)
        t = p.read_text()
        added = 0
        i = t.find('## Steps')
        assert i >= 0, f
        j = t.find('\n', i) + 1
        for b in blocks:
            if b[:30] not in t:
                t = t[:j] + '\n' + b + t[j:]
                added += 1
        p.write_text(t)
        print(f, 'blocks added:', added)

def main(argv):
    return entry(legacy, argv, minimum=1, maximum=None)

if __name__ == "__main__":
    sys.exit(entry(main))
