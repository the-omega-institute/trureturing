#!/usr/bin/env python3
'Portable rehead. See the openproblem README for inputs.'
from common import entry, read

def main(argv):
    import sys, re
    hf, rf, of, old, new, note = argv[1:7]
    rest = read(rf)
    assert re.fullmatch('[0-9a-f]{40}', old) and re.fullmatch('[0-9a-f]{40}', new)
    t = open(hf).read()
    n = t.count(old)
    assert n >= 1, ('old head absent', n)
    t = t.replace(old, new)
    a = 'The independent pre-freeze mirror checked that head and approved it.'
    assert t.count(a) == 1
    t = t.replace(a, f'The independent pre-freeze mirror ({note}) approves head `{new}`.')
    open(hf, 'w').write(t)
    open(of, 'w').write(t + rest)
    print('REHEAD_OK', n, new)

if __name__ == "__main__":
    import sys
    sys.exit(entry(main, minimum=6, maximum=6))
