#!/usr/bin/env python3
'Portable fix door base. See the openproblem README for inputs.'
from common import Context, REPO, entry

def main(argv):
    ctx = Context()
    import re, sys
    NOTE = '`origin/dev` is one remote-tracking ref shared by every worktree on this machine, and other seats fetch it while your build runs, so an ancestry check against it fails even when your merge is current. `git merge-base HEAD origin/dev` is the dev commit your tree actually merged and is always an ancestor of HEAD: pass that SHA as `BASE`. Freshness against the latest dev is the CI merge-tree check, not the door.'
    LAYOUT_OLD = 'Round 1 seat layout at `HEAD`: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli; `tests` is never nyxid-oracle.'
    LAYOUT_NEW = 'Round 1 seat layout at `HEAD`: architecture codex-cli, quality codex-cli, tests codex-cli. Review seats are verification seats, which CLAUDE.md §5.11 assigns to codex-cli only (nyxid-oracle takes reasoning tasks), so the round is judged by a single model family. No model-diversity claim is made for this round.'
    for f in argv[1:]:
        s = open(f).read()
        o = s
        s = re.sub('git merge-base --is-ancestor origin/dev HEAD && make (deposit-uncovered|deposit) (GID=\\S+?|ATOM_ID=\\S+ GID=\\S+?) BASE=origin/dev', 'B="$(git merge-base HEAD origin/dev)" && make \\1 \\2 BASE="$B"', s)
        s = s.replace('verify `git merge-base --is-ancestor origin/dev HEAD`,', 'pin `B="$(git merge-base HEAD origin/dev)"` (the dev commit this tree merged),')
        s = s.replace('make gate BASE="$(git rev-parse origin/dev^{commit})"', 'make gate BASE="$(git merge-base HEAD origin/dev)"')
        if 'Freshness against the latest dev is the CI merge-tree check, not the door.' not in s and 'BASE="$B"' in s:
            s = re.sub('(\\n    B=\\"\\$\\(git merge-base HEAD origin/dev\\)\\" && make deposit[^\\n]*\\n)', '\\1\\n' + NOTE.replace('\\', '\\\\') + '\n', s, count=1)
        s = re.sub('the brief\\s+names which seat is nyxid-oracle for round 1 \\(the orchestrator draws it before dispatching you\\); write\\s+`architecture nyxid-oracle / ChatGPT Pro, quality codex-cli, tests codex-cli` \\(or the drawn variant\\)', 'every review seat is codex-cli (CLAUDE.md §5.11); write the round-1 layout line exactly as this brief gives it', s)
        s = s.replace(LAYOUT_OLD, LAYOUT_NEW)
        left = len(re.findall('BASE=origin/dev\\b|is-ancestor origin/dev HEAD', s))
        open(f, 'w').write(s)
        print(f.split('/')[-1], 'changed' if s != o else 'unchanged', 'moving_ref_left', left)

if __name__ == "__main__":
    import sys
    sys.exit(entry(main, minimum=1, maximum=None))
