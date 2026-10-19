#!/usr/bin/env python3
"""Usage: file_prereg.py KEY:DRAFT [KEY:DRAFT ...]; OP_PENDING supplies drafts."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from common import Context, entry, fail, name, read


def table(path, numbers=False):
    records = {}
    for line in read(path).splitlines():
        if not line:
            continue
        cells = line.split('\t')
        if len(cells) != 2 or not all(cells) or cells[0] in records:
            fail(13, 'invalid or repeated TSV row: ' + str(path))
        if numbers and (not re.fullmatch(r'[1-9][0-9]*', cells[1])):
            fail(13, 'invalid issue number: ' + str(path))
        if numbers: name(cells[0])
        records[cells[0]] = cells[1]
    return records


def validate_body(body):
    if not body.strip():
        fail(13, 'empty preregistration body')
    for token in ('LEAN_BLOCK', 'COMPILE_LINE', 'SHA_'):
        if token in body:
            fail(13, 'unexpanded preregistration placeholder: ' + token)
    if re.search(r'(?<!`)`[ \t]*`(?!`)', body):
        fail(13, 'empty backtick pair in preregistration body')


def main(argv):
    ctx = Context(required=('gh',))
    value = os.environ.get('OP_PENDING')
    if not value or not Path(value).is_dir():
        fail(11, 'OP_PENDING must name an existing directory')
    pending = Path(value).resolve()
    titles = table(pending / 'post/titles.tsv')
    map_path = pending / 'post/issues.tsv'
    lock = pending / 'post/issues.lock'
    requests = []
    keys, selected_titles = set(), set()
    for arg in argv[1:]:
        if arg.count(':') != 1:
            fail(10, 'expected KEY:DRAFT')
        key, draft = map(name, arg.split(':'))
        if key in keys:
            fail(14, 'repeated key: ' + key)
        keys.add(key)
        body_path = pending / ('prereg-' + draft + '.md')
        body = read(body_path)
        validate_body(body)
        title = titles.get(body_path.name, '')
        if not title.strip():
            fail(11, 'missing title: ' + draft)
        if title in selected_titles:
            fail(14, 'duplicate requested title: ' + title)
        selected_titles.add(title)
        requests.append((key, title, body_path, body))
    try:
        lock.mkdir()
    except FileExistsError:
        fail(14, 'preregistration filing already locked: ' + str(lock))
    try:
        records = table(map_path, numbers=True) if map_path.exists() else {}
        # Query every new title before the first external write.
        for key, title, _, _ in requests:
            if key in records:
                continue
            result = subprocess.run(['gh', 'issue', 'list', '-R', ctx.slug, '--state', 'all',
                                     '--search', title + ' in:title', '--limit', '1000', '--json', 'number,title'],
                                    text=True, capture_output=True)
            if result.returncode:
                fail(16, 'preregistration duplicate search failed: ' + key)
            hits = json.loads(result.stdout)
            if not isinstance(hits, list):
                fail(13, 'invalid issue search response')
            if hits:
                fail(14, 'duplicate title search hit: ' + key)
        for key, title, body_path, body in requests:
            if key in records:
                print('PREREG_EXISTING', key, records[key])
                continue
            if read(body_path) != body:
                fail(14, 'draft changed while filing: ' + key)
            # File the validated snapshot, so an external editor cannot race gh.
            snapshot = lock / 'body.md'
            snapshot.write_text(body)
            result = subprocess.run(['gh', 'issue', 'create', '-R', ctx.slug, '--title', title,
                                     '--body-file', str(snapshot)], text=True, capture_output=True)
            if result.returncode:
                fail(16, 'preregistration create failed: ' + key)
            match = re.fullmatch(r'https://github\.com/' + re.escape(ctx.slug) + r'/issues/([1-9][0-9]*)', result.stdout.strip())
            if not match:
                fail(16, 'unexpected created issue URL; reconcile before retry: ' + key)
            records[key] = match[1]
            tmp = lock / 'issues.tsv.tmp'
            tmp.write_text(''.join(k + '\t' + n + '\n' for k, n in records.items()))
            tmp.replace(map_path)
            print('PREREG_FILED', key, match[1], flush=True)
    finally:
        for path in lock.iterdir():
            path.unlink()
        lock.rmdir()


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        from port_selftest import run
        sys.exit(run('file_prereg'))
    sys.exit(entry(main, minimum=1))
