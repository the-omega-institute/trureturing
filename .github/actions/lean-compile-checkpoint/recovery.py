"""Schedule missing native module facets against the original immutable source."""
from graphlib import TopologicalSorter
from itertools import batched
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path.cwd()
sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
import lean_compile_layers as layers


def plan(stage, destination):
    modules = layers.workspace_modules(ROOT)
    targets = layers.production_targets(ROOT, modules)
    graph = layers.scoped_imports(ROOT, modules, targets)
    part = layers.partition(graph, targets)[stage]
    build = ROOT / layers.PROJECT_BUILD
    boundary = 'D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData'
    consumers = sorted(n for n in part.owned if boundary in graph[n])
    focus = layers.import_closure(graph, [boundary, *consumers]) & part.owned if boundary in part.owned else set()
    ordered_graph = {n: sorted(graph[n]) for n in sorted(graph)}
    order = [n for n in TopologicalSorter(ordered_graph).static_order() if n in part.owned]
    prioritized = [n for n in order if n in focus] + [n for n in order if n not in focus]
    missing = [n for n in prioritized if not all((build / p).is_file() for p in layers.required_compiler_paths(n, modules[n]))]
    print(f'LEAN_LAYER_RECOVERY plan={stage} owned={len(order)} pending={len(missing)}', flush=True)
    for name in missing[:20]:
        print(f'LEAN_LAYER_RECOVERY pending={name}', flush=True)
    for name in consumers:
        print(f'LEAN_LAYER_RECOVERY imports_boundary={name} pending={name in missing}', flush=True)
    # Measure the affected dependency neighborhood one module at a time.
    singles = len([n for n in missing if n in focus])
    singles = max(3, singles)
    partitions = [[name] for name in missing[:singles]] + list(batched(missing[singles:], 12))
    destination.write_text(json.dumps([[f'@{modules[n].package}/+{n}:olean' for n in names] for names in partitions]))


def build(targets):
    print(f'LEAN_LAYER_RECOVERY batch={len(targets)} current={targets}', flush=True)
    directory = Path(os.environ['RUNNER_TEMP'])
    status = directory / 'lean-layer-batch-memory.txt'
    result = subprocess.run(['/usr/bin/time', '-f', '%M', '-o', str(status),
                             'bash', 'tools/scripts/worktree/lean-cache-run.sh', 'lake', '-d',
                             str(layers.REG_INSPECTOR), 'build', *targets])
    if status.exists():
        print(f'LEAN_LAYER_RECOVERY batch_peak_KiB={status.read_text().strip()}', flush=True)
    result.check_returncode()


if __name__ == '__main__':
    if sys.argv[1] == 'plan':
        plan(sys.argv[2], Path(sys.argv[3]))
    elif sys.argv[1] == 'build':
        build(sys.argv[2:])
    else:
        raise ValueError('invalid recovery operation')
