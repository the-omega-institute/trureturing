#!/usr/bin/env python3
'Portable exclusions compact. See the openproblem README for inputs.'
from common import Context, REPO, entry

def main(argv):
    ctx = Context()
    import re
    S = str(ctx.scratch)
    t = open(S + '/briefs/search-exclusions.md').read()
    if argv[1:2] == ['--preregistrations']:
        import json, subprocess
        issues = {}
        for query in ('Preregister in:title', 'preregistration in:title'):
            for issue in json.loads(subprocess.check_output(['gh', 'issue', 'list', '-R', ctx.slug, '--state', 'open', '--search', query, '--limit', '500', '--json', 'number,title'], text=True)):
                issues.setdefault(issue['number'], issue['title'])
        t += '\n' + '\n'.join(issues.values())
        argv = [argv[0], *argv[2:]]
    ids = sorted(set(re.findall('(?<![\\d.])(\\d{4}\\.\\d{4,5})(?!\\d)', t)) | set(re.findall('\\b((?:quant-ph|math|hep-th|cond-mat|math-ph|gr-qc|nlin|cs)(?:\\.[A-Z]{2})?/\\d{7})\\b', t)))
    import subprocess, sys
    repo = []
    if len(argv) > 1 and not re.fullmatch(r'\d{4}-\d{4}', argv[1]):
        from common import fail
        fail(13, 'window must be YYMM-YYMM')
    if len(argv) > 1 and re.fullmatch('\\d{4}-\\d{4}', argv[1]):
        lo, hi = argv[1].split('-')
        try:
            g = subprocess.run(['git', '-C', str(ctx.main), 'grep', '-h', '-o', '-E', '(^|[^0-9.])[0-9]{4}\\.[0-9]{4,5}([^0-9]|$)', 'origin/dev', '--', 'D5', 'Problems', 'Library'], capture_output=True, text=True, timeout=120).stdout
            repo = sorted({i for i in re.findall('(\\d{4}\\.\\d{4,5})', g) if lo <= i[:4] <= hi})
        except Exception as exc:
            from common import fail
            fail(16, str(exc))
    ids = sorted(set(ids) | set(repo))
    oeis = sorted(set(re.findall('\\bA\\d{6}\\b', t)))
    skip = re.compile('^(\\*\\*|Its |Route-only|Held lead|Already settled|Quick-track window|This |The |A |An |If |Exclude)')
    noid = []
    for line in t.split('\n'):
        l = line.strip().lstrip('-').strip()
        if not l or skip.match(l):
            continue
        if re.search('\\d{4}\\.\\d{4,5}|/\\d{7}|\\bA\\d{6}\\b', l):
            continue
        name = re.split(' — | \\(|: ', l)[0].strip(' .;')
        if 6 < len(name) <= 110:
            noid.append(name)
    out = ["Exclude (already preregistered, settled, triaged or held in this repository; do not propose again). Also check the repository's public open-problems page. arXiv identifiers: " + ', '.join(ids) + '.']
    if oeis:
        out.append('OEIS sequences: ' + ', '.join(oeis) + '.')
    if noid:
        out.append('Items without an arXiv identifier: ' + '; '.join(dict.fromkeys(noid)) + '.')
    open(S + '/briefs/search-exclusions-compact.md', 'w').write('\n\n'.join(out) + '\n')
    print('EXCL_COMPACT ids', len(ids), 'repo_ids_window', len(repo), 'oeis', len(oeis), 'named', len(noid))

if __name__ == "__main__":
    import sys
    sys.exit(entry(main, minimum=0, maximum=2))
