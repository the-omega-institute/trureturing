#!/usr/bin/env python3
"""Append completed-round results using the standing checker's parser.

Usage: standing_append.py PR SPEC.json
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
from common import Context, TOOLS, entry, load


def checker():
    spec = importlib.util.spec_from_file_location('standing_check', TOOLS / 'standing-check.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main(argv):
    ctx = Context(required=('gh',))
    pr, path = argv[1:]
    data = load(path)
    module = checker()
    response = subprocess.check_output(['gh', 'pr', 'view', pr, '-R', ctx.slug,
                                        '--json', 'body,headRefOid', '-q', '.'], text=True)
    current = json.loads(response)
    body = module.append_body(current['body'], current['headRefOid'], data)
    with tempfile.TemporaryDirectory(prefix='op-standing-') as tmp:
        out = Path(tmp) / 'body.md'
        out.write_text(body)
        subprocess.run(['gh', 'pr', 'edit', pr, '-R', ctx.slug,
                        '--body-file', str(out)], check=True, capture_output=True)
    print('edited', pr, 'head', current['headRefOid'])


if __name__ == '__main__':
    import sys
    sys.exit(entry(main, minimum=2, maximum=2))
