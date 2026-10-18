#!/usr/bin/env python3
'Portable fix review. See the openproblem README for inputs.'
from common import Context, REPO, entry

def main(argv):
    ctx = Context()
    import re, sys
    S = str(ctx.scratch)
    ga = open(S + '/briefs/goal-artifact.yaml').read()
    rev = ga[ga.index('  revisions:'):].rstrip('\n')
    rev = '\n'.join((l[2:] if l.startswith('  ') else l for l in rev.split('\n')))
    NEW = '**Carrier composition.** `CLAUDE.md` §5.11 assigns every verification task to codex-cli: review rounds (architecture, quality and tests seats), mirror checks, judgement-form checks and completion audits. nyxid-oracle takes reasoning tasks only. A review round uses three codex-cli verification seats. §5.2 and §5.8 then require the record to state that the round was judged by a single model family and makes no model-diversity claim; a record that states this is compliant. Treat as a finding only a record that claims model diversity for such a round, or that names a carrier the round did not use.'
    for f in argv[1:]:
        s = open(f).read()
        o = s
        s = re.sub('\\*\\*Carrier composition and its fallback\\.\\*\\*.*?with no fallback evidence\\.', NEW, s, flags=re.S)
        s = s.replace('\nrevisions: []\n', '\n' + rev + '\n', 1)
        open(f, 'w').write(s)
        print(f.split('/')[-1], 'changed' if s != o else 'unchanged', 'old_para_left', s.count('Carrier composition and its fallback'), 'verification_layout', s.count('Verification seats are codex-cli only'))

if __name__ == "__main__":
    import sys
    sys.exit(entry(main, minimum=1, maximum=None))
