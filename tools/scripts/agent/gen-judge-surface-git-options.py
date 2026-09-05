#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Regenerate tools/StrataLint.Engine/Rules/Trust/JudgeSurfaceGitOptionTables.cs (SL-030).

The per-verb option models are derived from git's own help so the closed set is git's, not a
hand-picked subset: `git <verb> -h` (parse-options short help) for cat-file, archive, worktree add,
checkout, restore and read-tree; the option headers of `man git-log` (revision and diff options
apply to `git show`) plus `git show -h` for show.

Usage:
  gen-judge-surface-git-options.py            # rewrite the table file from this machine's git
  gen-judge-surface-git-options.py --check    # exit 1 if the committed file differs (prints a diff)

Regenerate when the git version on the CI runner changes an option's arity; the header of the
generated file records the git version it came from. The tables fail closed on unknown options
(except for `show`, where an unknown option is read as a flag), so a newer git adding options
can only add findings on the judge surface, never hide one.
"""
import difflib
import io
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
TARGET = os.path.join(ROOT, 'tools', 'StrataLint.Engine', 'Rules', 'Trust', 'JudgeSurfaceGitOptionTables.cs')

SPEC_LONG = re.compile(r'^--(\[no-\])?([A-Za-z0-9][A-Za-z0-9-]*)(.*)$')
SPEC_SHORT = re.compile(r'^-([A-Za-z0-9])(.*)$')


def run(*argv, cwd=None):
    completed = subprocess.run(argv, capture_output=True, text=True, cwd=cwd or ROOT)
    return completed.stdout + completed.stderr


def diff_help():
    """`git diff -h` prints the full parse-options help of the diff options only outside a
    repository (inside one it prints the short usage), so it runs in a fresh empty directory."""
    return run('git', 'diff', '-h', cwd=tempfile.mkdtemp(prefix='sl030-git-help-'))


# A value placeholder right after the option name: `[=<n>]` (optional, attached), `=<x>`,
# `=[…]`, `=(…)`, `<x>` (attached), ` <x>`, ` (1|2|3)`, ` [(A|C…)]` (diff-filter's argh has its
# own brackets), ` blob|tree` (required).
PLACEHOLDER = re.compile(r'^(\[|=|<| <| \(| \[| blob\|tree)')


def arity_from_rest(rest, from_man=False):
    """parse-options prints a value placeholder right after the option: `--source <tree-ish>`,
    `--stage (1|2|3|all)`, `--[no-]path blob|tree`, `--decorate[=...]`; anything else after the
    name (`--relative-paths use relative paths…`) is the description, i.e. the option is a flag.
    Man pages write `--opt=<x>` for options that take a value (revision options accept it as
    `--opt <x>` too) and `--opt[=<x>]` for an optional attached value."""
    if not PLACEHOLDER.match(rest):
        return 'Flag'
    if rest.startswith('['):
        return 'OptionalAttached'
    return 'Required'


def parse_help(text, name):
    longs, shorts, numeric = {}, {}, False
    for line in text.split('\n'):
        if not line.startswith('    -'):
            continue
        # The description follows two or more spaces — or a single space when a long option
        # fills the whole option column (`--[no-]relative-paths use relative paths…`).
        spec = re.split(r'\s{2,}', line.strip(), maxsplit=1)[0]
        parts = []
        for part in spec.split(', '):
            if not part.startswith('-'):
                break
            glued = re.match(r'^(\S+) (?!<|\(|\[|blob\|tree)', part)
            parts.append(glued.group(1) if glued else part)
        # `-s, --[no-]source <tree-ish>`: the value placeholder is written once, after the last
        # alias, and applies to every alias on the line.
        last = parts[-1]
        m_last = SPEC_LONG.match(last) or SPEC_SHORT.match(last)
        line_arity = arity_from_rest(m_last.group(m_last.re.groups)) if m_last and last != '-NUM' else 'Flag'
        for part in parts:
            if part == '-NUM':
                numeric = True
                continue
            m = SPEC_LONG.match(part)
            if m:
                neg, key = m.group(1) is not None, m.group(2)
                longs[key] = (line_arity, neg and not key.startswith('no-'))
                continue
            m = SPEC_SHORT.match(part)
            if m:
                shorts[m.group(1)] = line_arity
                continue
            sys.exit(f'{name}: unrecognised option spec {part!r}')
    return longs, shorts, numeric


def merge_arity(current, new):
    """`--expand-tabs=<n>, --expand-tabs`: a bare spelling next to a value spelling means the value
    is optional and attached — the option must never consume the next word."""
    if current is None:
        return new
    if isinstance(current, tuple):
        current = current[0]
    if current == new:
        return new
    return 'OptionalAttached'


def parse_man(text):
    longs, shorts = {}, {}
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]
        if re.match(r'^       (-|--)[A-Za-z0-9]', line):
            header = line.strip()
            while header.endswith(',') and i + 1 < len(lines):
                i += 1
                header += ' ' + lines[i].strip()
            parts = [p.strip() for p in header.split(', ')]
            prose = re.search(r'\b(is|are|will|option|used|without|with)\b', header) or ' or ' in header
            if all(re.match(r'^-', p) for p in parts) and not prose:
                for p in parts:
                    if p.startswith('--') and ' ' in p and not p.split(' ', 1)[1].startswith('<'):
                        p = p.split(' ', 1)[0]
                    m = re.match(r'^--([A-Za-z0-9][A-Za-z0-9-]*)(.*)$', p)
                    if m:
                        longs[m.group(1)] = (merge_arity(longs.get(m.group(1)), arity_from_rest(m.group(2))), False)
                        continue
                    m = re.match(r'^-([A-Za-z0-9])(.*)$', p)
                    if m:
                        shorts[m.group(1)] = merge_arity(shorts.get(m.group(1)), arity_from_rest(m.group(2)))
        i += 1
    return longs, shorts


def emit_model(cs_name, longs, shorts, numeric, unknown_long_is_flag, unknown_short_is_flag, source):
    out = [f'    // Derived from {source}; regenerate with tools/scripts/agent/gen-judge-surface-git-options.py.',
           f'    private static readonly OptionModel {cs_name} = new(',
           '        new Dictionary<string, OptionSpec>(StringComparer.Ordinal)',
           '        {']
    for key in sorted(longs):
        arity, neg = longs[key]
        out.append(f'            ["{key}"] = new(OptionArity.{arity}, {"true" if neg else "false"}),')
    out += ['        },', '        new Dictionary<char, OptionArity>()', '        {']
    for c in sorted(shorts):
        out.append(f"            ['{c}'] = OptionArity.{shorts[c]},")
    out += ['        },',
            f'        NumericShort: {"true" if numeric else "false"},',
            f'        UnknownLongIsFlag: {"true" if unknown_long_is_flag else "false"},',
            f'        UnknownShortIsFlag: {"true" if unknown_short_is_flag else "false"});',
            '']
    return '\n'.join(out)


def generate():
    version = run('git', '--version').strip()
    models = []
    for verb, cs in [('cat-file', 'CatFileOptions'), ('archive', 'ArchiveOptions'), ('worktree add', 'WorktreeAddOptions'),
                     ('checkout', 'CheckoutOptions'), ('restore', 'RestoreOptions'), ('read-tree', 'ReadTreeOptions')]:
        longs, shorts, numeric = parse_help(run('git', *verb.split(' '), '-h'), verb)
        models.append(emit_model(cs, longs, shorts, numeric, False, False, f'`git {verb} -h` ({version})'))

    man = subprocess.run(['man', '-P', 'cat', 'git-log'], capture_output=True, text=True).stdout
    man = re.sub(r'.\x08', '', man)  # strip backspace-overstrike emphasis
    longs, shorts = parse_man(man)
    # `-<number>, -n <number>, --max-count=<number>` is one header the regex skips (it starts with `-<`).
    longs['max-count'] = ('Required', False)
    shorts['n'] = 'Required'
    # parse-options output is authoritative where it exists: `git show -h` (log options) and
    # `git diff -h` (diff options; `-U, --unified[=<n>]` is optional there, the man page says
    # `--unified=<n>`); the man page fills in the revision-walking options rev-list prints only
    # as a summary.
    for source in (run('git', 'show', '-h'), diff_help()):
        hl, hs, _ = parse_help(source, 'show')
        longs.update(hl)
        shorts.update(hs)
    models.append(emit_model('ShowOptions', longs, shorts, True, True, True,
                             f'`git show -h`, `git diff -h` and the option headers of `man git-log` ({version})'))
    return ('namespace StrataLint.Engine;\n\n'
            '// Per-verb option models: which git options are flags, which take a required value (as the next\n'
            '// word or attached with `=` / glued to a short option), and which take a value only when attached\n'
            '// (`--opt[=<v>]`). `Negatable` mirrors parse-options\' automatic `--no-<opt>` form. Generated from\n'
            '// git\'s own help output so the closed set is git\'s, not a hand-picked subset (review rounds 3–11:\n'
            '// every hand-written table missed a form). Regenerate: tools/scripts/agent/gen-judge-surface-git-options.py\n'
            'internal static partial class JudgeSurfaceRevisionScanner\n{\n' + '\n'.join(models) + '}\n')


def main():
    generated = generate()
    if '--check' in sys.argv[1:]:
        current = io.open(TARGET, encoding='utf-8').read() if os.path.exists(TARGET) else ''
        if current == generated:
            print('JudgeSurfaceGitOptionTables.cs is up to date')
            return 0
        sys.stdout.writelines(difflib.unified_diff(current.splitlines(True), generated.splitlines(True), 'committed', 'generated'))
        return 1
    io.open(TARGET, 'w', encoding='utf-8').write(generated)
    print(f'wrote {os.path.relpath(TARGET, ROOT)} ({generated.count(chr(10))} lines)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
