#!/usr/bin/env python3
"""Render a codex search brief through the canonical search renderer.

Usage: codex_search.py LETTER ROUND [deep|quick] [WINDOW]
"""
import os
from pathlib import Path
import subprocess
from common import Context, TOOLS, entry, fail, name, read


def main(argv):
    ctx = Context(required=('gh',))
    letter, round_number = argv[1:3]
    name(letter)
    if not round_number.isdigit() or int(round_number) < 1:
        fail(13, 'positive round required')
    track = argv[3] if len(argv) > 3 else 'deep'
    if track not in ('deep', 'quick'):
        fail(13, 'track must be deep or quick')
    required = ['OP_SEARCH_WORKTREE', 'OP_SEARCH_OUTPUT_DIR']
    if track == 'deep':
        required.append('OP_CODEX_EXCLUSIONS')
    for key in required:
        if not os.environ.get(key):
            fail(11, key + ' required')
    exclusions = read(os.environ['OP_CODEX_EXCLUSIONS']).rstrip('\n') if track == 'deep' else ''
    block = ctx.block('mathdb-access-block.md').read_text()
    worktree = os.environ['OP_SEARCH_WORKTREE']
    output_dir = os.environ['OP_SEARCH_OUTPUT_DIR']
    out = ctx.scratch / 'briefs' / f'codex-search-{letter}-r{round_number}.md'
    seat = f'codex-cli:{ctx.prefix}codex-search-{letter}-r{round_number}'
    args = ['/bin/bash', str(TOOLS / 'render-search-brief.sh'), seat, str(out), track]
    if len(argv) > 4:
        args.append(argv[4])
    subprocess.run(args, check=True, stdout=subprocess.DEVNULL)
    text = out.read_text()
    first = 'You are one independent search seat (nyxid-oracle, ChatGPT Pro).'
    if text.count(first) != 1:
        fail(13, 'search carrier anchor missing or ambiguous')
    text = text.replace(first, f'You are one independent search seat (codex-cli, thinking stage, read-only). Write nothing outside `{output_dir}`; make no commits, pushes or GitHub writes.')
    start = text.index('Read single files at')
    end = text.index('Read this repository first.') if track == 'deep' else text.index('\n\n', start)
    extra = (f'Your worktree `{worktree}` is a detached checkout of `origin/dev`. Read the repository locally, use web search and arXiv for the literature, '
             'and run `ls Problems/`, `gh issue list --state all --search "Preregister in:title" --limit 500` and `gh issue list --state all --search "preregistration in:title" --limit 500` yourself for the exclusion checks.')
    if track == 'deep':
        extra += (' Also skip these candidates, which this session has already assessed (deferred, yielded to another active driver, or famous-hard): '
                  + exclusions + '\n\n')
    text = text[:start] + extra + text[end:]
    text += block
    out.write_text(text)
    print(out, len(text))


if __name__ == '__main__':
    import sys
    sys.exit(entry(main, minimum=2, maximum=4))
