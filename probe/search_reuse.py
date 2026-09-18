"""Count reproducible repository and pinned Mathlib reuse searches."""
import json
import shlex
import subprocess
from pathlib import Path

rows = []
queries = [
    ('topic', r'(?i)stack.?sort|vincular|2410\.17057'),
    ('patterns', r'(?i)permutation.{0,25}pattern|pattern.{0,25}avoid'),
    ('reuse', r'List\.(Perm|permutations)|Equiv\.Perm|card_le_card|card_le_card_of_injOn'),
    ('positive_control', r'Nat\.add_comm'),
]
for root, paths in [('.', ['D5', 'Blueprint', 'Library', 'Problems', 'docs/develop/theory', 'Evidence', 'Meta/Digestion']), ('.lake/packages/mathlib', ['Mathlib'])]:
    for label, pattern in queries:
        argv = ['git', 'grep', '-n', '-P', pattern, '--', *paths]
        p = subprocess.run(argv, cwd=root, text=True, capture_output=True)
        lines = p.stdout.splitlines()
        row = dict(root=root, label=label, pattern=pattern, command=shlex.join(argv), exit=p.returncode, line_hits=len(lines), file_hits=len({x.split(':', 1)[0] for x in lines}), sample=lines[:12], stderr=p.stderr)
        rows.append(row)
        print(root, label, p.returncode, len(lines), row['file_hits'], flush=True)
Path('probe/dedupe.json').write_text(json.dumps(rows, indent=2) + '\n')
