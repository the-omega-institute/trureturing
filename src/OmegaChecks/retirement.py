"""Measure the protected OmegaMath retirement scope independently of the candidate."""
import argparse
from collections import defaultdict, deque
from functools import lru_cache
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from portable import BASIS, ROOT, atomic_json, consumers, declaration_rows, import_graph, read_measurement, root


SOURCE_DIRS = ('src', 'strict', 'D5', 'Reg')


def reverse_closure(graph, roots):
    reverse = defaultdict(set)
    for name, imports in graph.items():
        for dependency in imports:
            reverse[dependency].add(name)
    affected = set(roots)
    pending = deque(roots)
    while pending:
        importers = reverse[pending.popleft()] - affected
        affected.update(importers)
        pending.extend(importers)
    return affected


def affected_modules(graph):
    providers = {name for name in graph if root(name) == 'OmegaMath'}
    return sorted(providers), sorted(reverse_closure(graph, providers) - providers)


def protected_inventory(base, repository=ROOT):
    """Read import headers and frozen membership from Git at the same immutable commit."""
    commit = subprocess.check_output(['git', 'rev-parse', '--verify', '--end-of-options',
                                      base + '^{commit}'], cwd=repository, text=True).strip()
    return _protected_inventory(commit, repository)


@lru_cache(maxsize=4)
def _protected_inventory(commit, repository):
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=repository, text=True)

    pin = json.loads(git('show', f'{commit}:Meta/tools-release.json'))
    tools = repository / 'tools'
    if (tools / '.release-sha256').read_text().strip() != pin['sha256']:
        raise ValueError(f'need protected inspector interface from tools {pin["version"]} for {commit}')
    interface = tools / 'lean-inspector-interface'
    if not (interface / 'lakefile.toml').is_file():
        raise FileNotFoundError(f'protected inspector interface missing at {interface}')
    with tempfile.TemporaryDirectory(prefix='omega-retirement-') as temp:
        snapshot = Path(temp)
        pathspecs = [f':(glob){path}/**/*.lean' for path in SOURCE_DIRS]
        with subprocess.Popen(['git', 'archive', commit, '--', *pathspecs, 'Trureturing.lean',
                               'lean-toolchain'], cwd=repository, stdout=subprocess.PIPE) as archive:
            subprocess.run(['tar', '-x', '-C', snapshot], stdin=archive.stdout, check=True)
            if archive.wait():
                raise RuntimeError(f'failed to read Lean inputs at {commit}')
        files = [(path, path.relative_to(snapshot)) for path in sorted(snapshot.rglob('*.lean'))]
        files.extend((path, path.relative_to(interface)) for path in
                     [*interface.glob('LeanInformationAuditInterface.lean'),
                      *sorted((interface / 'LeanInformationAuditInterface').rglob('*.lean'))])
        graph = defaultdict(set)
        names = {}
        for start in range(0, len(files), 2048):
            batch = files[start:start + 2048]
            result = subprocess.check_output(['lean', '--deps-json', '--stdin'], cwd=snapshot, text=True,
                                             input=''.join(f'{path}\n' for path, _ in batch))
            for (path, relative), row in zip(batch, json.loads(result)['imports'], strict=True):
                if row['errors']:
                    raise ValueError(f'{relative} at {commit}: {row["errors"]}')
                parts = relative.with_suffix('').parts
                name = '.'.join(parts[1:] if parts[0] in ('src', 'strict') else parts)
                graph[name].update(entry['module'] for entry in row['result']['imports'])
                if path.is_relative_to(snapshot):
                    names[name] = relative.as_posix()
    providers, consumers = affected_modules(graph)
    frozen_paths = set(git('ls-tree', '-r', '--name-only', '-z', commit, '--',
                           'Golden/Frozen/state').split('\0'))
    frozen = {}
    for name in consumers:
        path = f'Golden/Frozen/state/{names.get(name)}.json'
        if path in frozen_paths:
            frozen[name] = json.loads(git('show', f'{commit}:{path}'))
    standard = reverse_closure(graph, {n for n in graph if root(n) in BASIS})
    clients = sorted(n for n in standard if root(n) in {'D5', 'Reg', 'Trureturing'}
                     or n.startswith('OmegaChecks.Portable.'))
    selected = set(providers + consumers + clients)
    return dict(commit=commit, providers=providers, consumers=consumers, standardConsumers=clients, frozen=frozen,
                imports={name: sorted(graph[name]) for name in sorted(selected)})


def protected_omega_consumers(base):
    inventory = protected_inventory(base)
    return set(inventory['consumers']) | set(inventory['standardConsumers'])


def legacy_providers(base):
    return set(protected_inventory(base)['providers'])


def reconcile(protected, old_rows, comparisons):
    """Account for every included compiled declaration and every protected frozen key."""
    old_names = set(protected['providers']) | set(protected['consumers'])
    if {row['module'] for row in old_rows} != old_names:
        raise ValueError('protected compiled inventory does not cover the protected import graph')
    checked = {(row['module'], row['nameKey']): row for row in comparisons}
    if len(checked) != len(comparisons):
        raise ValueError('duplicate compiled comparison row')
    results = []
    for module in old_rows:
        name = module['module']
        original = declaration_rows(module)
        frozen = protected['frozen'].get(name, {}).get('declarations', [])
        for entry in frozen:
            measured = original.get(entry['declaration_name_key'])
            if not measured or measured['kind'] != entry['kind']:
                raise ValueError(f"protected frozen declaration missing from {name}: {entry['declaration_name_key']}")
        for key, old in original.items():
            if not old['includeInStatement']:
                continue
            row = checked.get((name, key))
            if row is None:
                row = dict(module=name, nameKey=key, obligation='missing compiled comparison')
            results.append(dict(row, kind=old['kind'], protectedStatement=old['statementTypeAddress']))
    return results


def lake_command(stage, reg=False):
    return ['lake', '-d', str(stage / 'Reg')] if reg else ['lake']


def build(stage, modules):
    for reg in [False, True]:
        targets = sorted('+' + name for name in modules if (root(name) == 'Reg') == reg)
        if targets:
            subprocess.run([*lake_command(stage, reg), 'build', *targets], cwd=stage, check=True)


def lean_path(stage, reg):
    return subprocess.check_output([*lake_command(stage, reg), 'env', 'printenv', 'LEAN_PATH'],
                                   cwd=stage, text=True).strip()


def publication_candidates(base, original):
    """Discover potential destinations, including additions in an uncommitted migration."""
    paths = set(subprocess.check_output(['git', 'diff', '--name-only', '-z', base, '--'],
                                        cwd=ROOT, text=True).split('\0'))
    paths.update(subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z'],
                                         cwd=ROOT, text=True).split('\0'))
    present = set()
    for name in original:
        path = Path(*name.split('.')).with_suffix('.lean')
        if any((ROOT / prefix / path).is_file() for prefix in ['', 'src']):
            present.add(name)
    for path in paths:
        if path.endswith('.lean') and path.startswith(('src/OmegaMathlib/', 'D5/', 'Reg/')) and (ROOT / path).is_file():
            present.add(path.removeprefix('src/').removesuffix('.lean').replace('/', '.'))
    return sorted(present)


def standard_scope(inventory, changed_paths):
    from scope import module_path
    changed = {name for path in changed_paths if (name := module_path(path))}
    if not changed:
        return [], []
    _, graph = import_graph('lean', with_reg=True)
    protected = set(inventory['standardConsumers'])
    in_scope = (protected | set(consumers(graph))) & (
        reverse_closure(inventory['imports'], changed) | reverse_closure(graph, changed))
    protected_files = set(subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', '-z',
                               inventory['commit']], cwd=ROOT, text=True).split('\0'))
    old = sorted(n for n in in_scope if any(prefix + n.replace('.', '/') + '.lean' in protected_files
                                            for prefix in ['', 'src/']))
    return old, sorted(n for n in old if n in graph)


def transferred_freezes(rows, providers, state_dir):
    states = {}
    for row in rows:
        owner = row.get('candidateModule', '')
        if row['module'] not in providers or root(owner) != 'D5' or 'comparison' not in row:
            continue
        if owner not in states:
            state = state_dir / (owner.replace('.', '/') + '.lean.json')
            entries = json.loads(state.read_text())['declarations'] if state.is_file() else []
            states[owner] = {(e['declaration_name_key'], e['kind']) for e in entries}
        if (row['candidateKey'], row['kind']) not in states[owner]:
            row['obligation'] = f'transferred declaration missing from canonical freeze of {owner}'
            del row['comparison']


def verify(inventory, stage, temp, standard=None):
    if standard is None:
        old = inventory['providers'] + inventory['consumers']
        new = publication_candidates(inventory['commit'], old)
    else:
        old, new = standard
    # Publication and removal are separate from equality of statements across revisions.
    inventory['retainedProviders'] = [n for n in new if root(n) == 'OmegaMath']
    build(stage, old)
    build(ROOT, [*new, 'OmegaChecks.Interface', 'OmegaChecks.ObjectOrigins'])
    old_path = lean_path(stage, any(root(n) == 'Reg' for n in old))
    new_path = lean_path(ROOT, any(root(n) == 'Reg' for n in new))
    request = temp / 'comparison.json'
    output = temp / 'rows.json'
    request.write_text(json.dumps(dict(protectedPath=old_path, candidatePath=new_path,
                                       protectedModules=old, candidateModules=new, standardUses=standard is not None)))
    subprocess.run(['lake', 'env', 'lean', '--run', 'src/OmegaChecks/RetiredDeclarations.lean', request, output],
                   cwd=ROOT, check=True)
    comparisons = json.loads(output.read_text())
    if standard is not None:
        inventory['declarations'] = comparisons
        return
    inspector = ROOT / '.lake/build/lean-inspector/producer/bin/reportInspector'
    old_request = temp / 'protected-modules.json'
    old_measurement = temp / 'protected-objects.json'
    old_request.write_text(json.dumps(old))
    subprocess.run([inspector, '--frozen-dependencies-v1', old_request, old_measurement],
                   cwd=stage, env={**os.environ, 'LEAN_PATH': old_path}, check=True)
    measured = read_measurement(old_measurement, old)
    inventory['declarations'] = reconcile(inventory, measured, comparisons)
    transferred_freezes(inventory['declarations'], set(inventory['providers']), ROOT / 'Golden/Frozen/state')
    missing_files = set(inventory['frozen']) - set(new)
    for name in inventory['frozen']:
        path = ROOT / 'Golden/Frozen/state' / (name.replace('.', '/') + '.lean.json')
        if not path.is_file():
            missing_files.add(name)
    inventory['missingFrozenModules'] = sorted(missing_files)


def verified_snapshot(inventory, temp, standard=None):
    """Compile protected source bytes in a separate Lake build directory."""
    stage = temp / 'base'
    stage.mkdir()
    paths = [*SOURCE_DIRS, 'Trureturing.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
    with subprocess.Popen(['git', 'archive', inventory['commit'], '--', *paths],
                          cwd=ROOT, stdout=subprocess.PIPE) as archive:
        subprocess.run(['tar', '-x', '-C', stage], stdin=archive.stdout, check=True)
        if archive.wait():
            raise RuntimeError('failed to export the protected build')
    for filename in ['lean-toolchain', 'lake-manifest.json']:
        if (stage / filename).read_bytes() != (ROOT / filename).read_bytes():
            raise ValueError(f'prepare the protected version of {filename} before comparing the two builds')
    (stage / '.lake').mkdir()
    (stage / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
    # A symlink to the interface directory itself would resolve its local package dependency against the candidate.
    shutil.copytree(ROOT / 'tools/lean-inspector-interface', stage / 'tools/lean-inspector-interface',
                    ignore=shutil.ignore_patterns('.lake'))
    verify(inventory, stage, temp, standard)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--protected-base', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--verify', action='store_true', help='build and compare old and new publication artifacts')
    parser.add_argument('--changed-paths', type=Path, help='additional NUL-separated changed paths from CI')
    args = parser.parse_args()
    inventory = dict(protected_inventory(args.protected_base))
    if args.verify:
        paths = set(subprocess.check_output(['git', 'diff', '--name-only', '-z', inventory['commit']],
                                            cwd=ROOT, text=True).split('\0'))
        if args.changed_paths:
            raw = args.changed_paths.read_bytes()
            if raw and not raw.endswith(b'\0'):
                raise ValueError('changed paths must be NUL-terminated')
            paths.update(raw.decode().split('\0'))
        standard = None if inventory['providers'] else standard_scope(inventory, paths)
        if standard is None or standard[0]:
            with tempfile.TemporaryDirectory(prefix='omega-migration-') as temporary:
                verified_snapshot(inventory, Path(temporary), standard)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    atomic_json(args.output, inventory)
    print(f"{inventory['commit']}: {len(inventory['providers'])} provider modules, "
          f"{len(inventory['consumers'])} consumer modules, {len(inventory['frozen'])} frozen modules")
    pending = [row for row in inventory.get('declarations', []) if 'obligation' in row]
    for row in pending:
        print(f"{row['module']} {row.get('name', row['nameKey'])}: {row['obligation']}")
    if missing := inventory.get('missingFrozenModules'):
        print(f'missing frozen declarations or module files: {missing}')
    if remaining := inventory.get('retainedProviders'):
        print(f'legacy provider modules remain: {remaining}')
    if pending or inventory.get('missingFrozenModules') or inventory.get('retainedProviders'):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
