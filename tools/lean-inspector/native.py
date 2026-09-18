#!/usr/bin/env python3
"""Production actions for Lake's Inspector facets; Lake owns module invalidation."""
from __future__ import annotations

import json
import hashlib
from contextlib import contextmanager
from functools import lru_cache
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import zipfile
import zlib

# Match zipfile's optional LZMA support; importing the producer must also work
# on Python installations without that decoder.
try:
    from lzma import LZMAError
except ImportError:
    LZMA_ERRORS = ()
else:
    LZMA_ERRORS = (LZMAError,)

ROW_ERRORS = (OSError, UnicodeError, ValueError, KeyError, TypeError,
              zipfile.BadZipFile, zlib.error, NotImplementedError) + LZMA_ERRORS

import materials
import publication as public

selection = public.selection
ROW_SUFFIXES = ('', '.materials.zip', '.provenance.json')
UTILITY_FIELDS = {'modulePath', 'claimGid', 'claimModule', 'claimSelector', 'claimSourcePath',
                  'claimSourceSha256', 'resultGid', 'resultModule', 'resultSelector'}


def activity(kind, count):
    """Invocation-local work counts; these never participate in reuse decisions."""
    path = os.environ.get('STRATALINT_INSPECTOR_ACTIVITY')
    if path:
        with Path(path).open('a', encoding='utf-8') as target:
            target.write(json.dumps({'kind': kind, 'count': count}) + '\n')


@contextmanager
def phase(name):
    """Flush invocation phase boundaries independently of buffered process IO."""
    path = os.environ.get('STRATALINT_INSPECTOR_PHASES')

    def emit(boundary, **fields):
        if path:
            with Path(path).open('a', encoding='utf-8') as target:
                target.write(json.dumps(dict(phase=name, boundary=boundary,
                    monotonic_ms=time.monotonic_ns() // 1_000_000, **fields)) + '\n')

    emit('start')
    success = False
    try:
        yield
        success = True
    finally:
        emit('finish', success=success)


def state(root):
    return Path(root) / '.lake/build/lean-inspector'


def write_if_changed(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() == data:
        return
    # Never mutate a possible restored hard link in place.
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_bytes(data)
    os.replace(temporary, path)


def _safe_path(root, relative):
    if (not isinstance(relative, str) or not relative or Path(relative).is_absolute()
            or '..' in Path(relative).parts):
        raise ValueError('unsafe native input path: ' + repr(relative))
    path = Path(root)
    for part in Path(relative).parts:
        path = path / part
        if path.is_symlink():
            raise ValueError('native input traverses a symlink: ' + relative)
    return path


def _regular_file(path, root):
    relative = path.relative_to(root).as_posix()
    path = _safe_path(root, relative)
    if not path.exists():
        return None
    info = path.stat()
    if not stat.S_ISREG(info.st_mode):
        raise ValueError('nonregular native source: ' + relative)
    data = path.read_bytes()
    return dict(path=relative, mode=stat.S_IMODE(info.st_mode),
                sha256=hashlib.sha256(data).hexdigest(),
                git_blob=hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest())


def _walk_regular(root, excluded):
    """Source namespaces include ignored additions; exclusions come from Lake."""
    entries = []
    if not root.exists():
        return entries
    if root.is_file():
        return [_regular_file(root, root.parent)]
    if not root.is_dir():
        raise ValueError('native source root is not a directory')
    def unreadable(error):
        raise error
    for directory, dirs, files in os.walk(root, followlinks=False, onerror=unreadable):
        kept = []
        for name in dirs:
            child = Path(directory) / name
            if name == '.git' or child in excluded:
                continue
            if child.is_symlink():
                raise ValueError('symlink in native source namespace: ' + str(child))
            kept.append(name)
        dirs[:] = kept
        for filename in files:
            if filename.endswith('.lean'):
                entries.append(_regular_file(Path(directory) / filename, root))
    return entries


def _git_snapshot(package_dir, entries, package, roots, excluded):
    """Check actual bytes/modes against the pinned commit, never path membership alone."""
    unavailable = dict(kind='unavailable', immutable=False, head=None, tree=None, blobs={})
    pin = package['pin']
    if not isinstance(pin, dict) or pin.get('type') != 'git':
        return unavailable
    try:
        def git(*args):
            return subprocess.check_output(['git', '-C', str(package_dir), *args], stderr=subprocess.PIPE)
        head = git('rev-parse', '--verify', 'HEAD').decode().strip()
        tree = git('rev-parse', '--verify', 'HEAD^{tree}').decode().strip()
        top = Path(git('rev-parse', '--show-toplevel').decode().strip()).resolve()
        listing = git('ls-tree', '-r', '-z', 'HEAD', '--')
    except (OSError, subprocess.SubprocessError):
        return unavailable
    blobs = {}
    for record in listing.split(b'\0'):
        if not record:
            continue
        header, path = record.split(b'\t', 1)
        mode, kind, oid = header.split(b' ', 2)
        if kind == b'blob':
            blobs[path.decode('utf-8')] = dict(oid=oid.decode('ascii'), mode=mode.decode('ascii'))
    expected_dir = top / (pin.get('subDir') or '.')
    immutable = (head == pin.get('rev') and expected_dir == package_dir
                 and package['remote_url'] == pin.get('url') and package['scope'] == pin.get('scope'))
    by_path = {item['path']: item for item in entries}
    for item in entries:
        blob = blobs.get(item['path'])
        mode = '100755' if item['mode'] & 0o111 else '100644'
        immutable = immutable and blob == dict(oid=item['git_blob'], mode=mode)
    # A missing tracked source/config is a changed checkout, never absence.
    for path in blobs:
        absolute = package_dir / path
        relevant = path in package['config_paths'] or (path.endswith('.lean') and
            any(absolute.is_relative_to(root) for root in roots) and
            not any(absolute.is_relative_to(directory) for directory in excluded))
        if relevant and path not in by_path:
            immutable = False
    return dict(kind='git', immutable=bool(immutable), head=head, tree=tree, blobs=blobs)


def _descriptor(value):
    if isinstance(value, dict) and set(value) == {'descriptor', 'resolver'}:
        value = value['descriptor']
    materials.require_keys(value, {'kind', 'packages', 'excluded_dirs', 'complete_defaults'},
                           'native Lake input population')
    if value['kind'] != selection.NATIVE_INPUT_KIND or type(value['complete_defaults']) is not bool:
        raise ValueError('invalid native Lake population')
    owners, dirs = set(), set()
    for package in value['packages']:
        materials.require_keys(package, {'owner', 'dir', 'source_roots', 'config_paths', 'modules',
                                         'remote_url', 'scope', 'pin'}, 'native package input')
        if not isinstance(package['owner'], str) or not package['owner'] or package['owner'] in owners:
            raise ValueError('duplicate or invalid native owner')
        if package['dir'] in dirs:
            raise ValueError('ambiguous native package directory')
        owners.add(package['owner']); dirs.add(package['dir'])
    return value


def resolver_inputs(root, descriptor):
    """Current resolver/config bytes, including absent alternate configuration files."""
    root = Path(root)
    result = {}
    for package in descriptor['packages']:
        directory = _safe_path(root, package['dir'])
        config = {}
        for relative in sorted(set(package['config_paths'])):
            path = _safe_path(directory, relative)
            entry = _regular_file(path, directory)
            config[relative] = entry
        result[package['owner']] = config
    # Root toolchain/configuration also binds an absent-package seed.
    inputs = selection.Selection(root)
    result['$root'] = {path: _regular_file(inputs.safe_file(path), root)
        for path in sorted(inputs.expand('config_inputs'))}
    return result


def native_population(root, descriptor):
    """Snapshot only native-owned namespaces; this does not resolve modules."""
    if descriptor is None:
        return None
    descriptor = _descriptor(descriptor)
    root = Path(root).resolve()
    # Lake permits a package buildDir to point at a workspace-owned parent.
    # Normalize those native output paths only; input owner paths stay strict.
    excluded = {_safe_path(root, os.path.normpath(path)) for path in descriptor['excluded_dirs']}
    package_dirs = {_safe_path(root, package['dir']) for package in descriptor['packages']}
    packages = []
    for package in descriptor['packages']:
        package_dir = _safe_path(root, package['dir'])
        base = dict(package)
        if not package_dir.exists():
            packages.append(dict(base, status='absent'))
            continue
        if not package_dir.is_dir():
            raise ValueError('native package path is not a directory')
        roots = sorted({_safe_path(root, path) for path in package['source_roots']})
        if any(not path.is_relative_to(package_dir) for path in roots):
            raise ValueError('native source root escapes package owner')
        entries = {}
        for source in roots:
            # Explicit native roots can live inside another package or lakeDir.
            ignored = {path for path in excluded | package_dirs
                       if path != source and not source.is_relative_to(path)}
            for item in _walk_regular(source, ignored):
                item['path'] = ((source.parent if source.is_file() else source) / item['path']).relative_to(package_dir).as_posix()
                entries[item['path']] = item
        configs = []
        for relative in sorted(set(package['config_paths'])):
            item = _regular_file(_safe_path(package_dir, relative), package_dir)
            if item is not None:
                configs.append(item)
        for module in package['modules']:
            materials.require_keys(module, {'name', 'path'}, 'native package module')
            _safe_path(package_dir, module['path'])
            if module['path'] not in entries:
                raise ValueError('native module source is absent: ' + module['name'])
        snapshot = _git_snapshot(package_dir, list(entries.values()) + configs,
                                 package, roots, excluded)
        packages.append(dict(base, status='materialized',
            sources=sorted(entries.values(), key=lambda item: item['path']), config=configs, git=snapshot))
    return dict(kind=descriptor['kind'], descriptor=descriptor,
                resolver=resolver_inputs(root, descriptor), packages=sorted(packages, key=lambda item: item['owner']))


def current_population(root, previous=None):
    """Offline validation of producer-bound native resolution; never stored-snapshot fallback."""
    path = state(root) / 'lake-inputs.json'
    if path.exists() or path.is_symlink():
        if path.is_symlink():
            raise ValueError('nonregular native resolver evidence')
        bound = public.read_json(path.read_bytes())
        materials.require_keys(bound, {'descriptor', 'resolver'}, 'native resolver evidence')
    elif previous is not None:
        bound = {key: previous[key] for key in ('descriptor', 'resolver')}
    else:
        raise ValueError('native resolver evidence is absent')
    descriptor = _descriptor(bound)
    current = native_population(root, descriptor)
    prior = {p['owner']: p for p in (previous or {}).get('packages', [])}
    for index, package in enumerate(current['packages']):
        owner = package['owner']
        if package['status'] == 'absent':
            old = prior.get(owner)
            if (old is None or not isinstance(old.get('pin'), dict) or old['pin'].get('type') != 'git'
                    or not old.get('git', {}).get('immutable')
                    or old['git']['head'] != old['pin']['rev']):
                raise ValueError('absent package lacks immutable producer snapshot')
            current['packages'][index] = old
            current['resolver'][owner] = bound['resolver'][owner]
    if current['resolver'] != bound['resolver']:
        raise ValueError('native resolver configuration changed')
    return current


def immutable_population(population):
    return population['descriptor']['complete_defaults'] and all(
        not isinstance(p['pin'], dict) or p['pin'].get('type') != 'git' or p['git']['immutable']
        for p in population['packages'])


@phase('native-inputs')
def prepare(root, lake_inputs=None):
    root = Path(root).resolve()
    inputs = selection.Selection(root)
    inputs.validate('lean-report')
    modules = inputs.modules()
    producer = os.environ.get('STRATALINT_LEAN_PRODUCER_DLL')
    if producer:
        if not Path(producer).is_absolute() or not Path(producer).is_file():
            raise ValueError('candidate Lean producer must be an existing absolute path')
        command = ['dotnet', producer]
    else:
        command = ['dotnet', 'run', '--project', str(root / 'tools/StrataLint.Lean/StrataLint.Lean.csproj'),
            '--configuration', 'Release', '--no-build', '--no-restore', '--no-launch-profile', '--']
    result = subprocess.run([*command, 'lean-utility-input'],
        cwd=root, stdout=subprocess.PIPE, check=True)
    utilities = public.read_json(result.stdout)
    if not isinstance(utilities, list):
        raise ValueError('utility input must be an array')
    by_path = {}
    for utility in utilities:
        materials.require_keys(utility, UTILITY_FIELDS, 'authoritative utility input')
        if any(not isinstance(value, str) or not value for value in utility.values()):
            raise ValueError('incomplete utility input')
        path = utility['modulePath']
        if path in by_path:
            raise ValueError('duplicate utility obligation')
        claim = inputs.safe_file(utility['claimSourcePath'])
        if utility['claimSourceSha256'] != 'sha256:' + public.digest(claim):
            raise ValueError('stale authoritative claim source')
        by_path[path] = utility
    for name, path in sorted(modules.items()):
        utility = [by_path[path]] if path in by_path else []
        write_if_changed(state(root) / 'inputs' / (name + '.json'), materials.canonical_json({
            'utilities': utility, 'claims': sorted({u['claimModule'] for u in utility}), 'source_path': path}))
    write_if_changed(state(root) / 'compatibility', (inputs.compatibility() + '\n').encode('ascii'))
    # Membership and full config identity affect aggregation only. Each module
    # traces compatibility, source, utility inputs and Lake's compiler dependencies.
    descriptor = None
    if lake_inputs is not None:
        descriptor = public.read_json(Path(lake_inputs).read_bytes())
    population = native_population(root, descriptor)
    if population is not None:
        write_if_changed(Path(lake_inputs), materials.canonical_json({
            'descriptor': population['descriptor'], 'resolver': population['resolver']}))
    write_if_changed(state(root) / 'inputs.json', materials.canonical_json({
        'modules': sorted(modules),
        'configs': inputs.expand('config_inputs'), 'coordinates': public.coordinates(root),
        **({'native_inputs': population} if population is not None else {})}))


@lru_cache(maxsize=None)
def source_inventory(root):
    # Expanded once per native invocation, never mixed into the aggregate
    # trace: adding an unused producer helper is still a compatible change.
    inputs = selection.Selection(root)
    return set(inputs.dependency_sources()), set(inputs.modules().values())


def source_context(root, *, require_snapshot=False):
    config = public.read_json((state(root) / 'inputs.json').read_bytes())
    population = config.get('native_inputs')
    if population is not None:
        current = current_population(root)
        if require_snapshot and current != population:
            raise ValueError('native inputs changed during production')
        population = current
    by_module = {}
    for package in (population or {}).get('packages', []):
        sources = {source['path']: source for source in package.get('sources', [])}
        for module in package['modules']:
            source = sources.get(module['path'])
            if source is not None:
                by_module[(package['owner'], module['name'], module['path'])] = (package, source)
    return by_module


def input_sources(root, utility_path, *, context=None):
    """Capture Lake's local source closure, bounded by explicit registration.

    Other reported sources are already bound by the complete exported report
    address. Keep their closure out of each row's sidecar to avoid quadratic
    duplication; native compiler traces still govern row invalidation.
    """
    allowed, reported = source_inventory(str(root))
    record = public.read_json(Path(utility_path).read_bytes())
    source_data = public.read_json(Path(str(utility_path) + '.sources.json').read_bytes())
    materials.require_keys(source_data, {'local', 'external'}, 'native dependency source closure')
    local_paths, external = source_data['local'], source_data['external']
    materials.require_sorted_strings(sorted(set(local_paths)), 'native dependency sources')
    if set(local_paths) - allowed:
        raise ValueError('unregistered native dependency sources: ' + ', '.join(sorted(set(local_paths) - allowed)))
    selected = (set(local_paths) - reported) | {record['source_path']}
    local = {path: public.digest(Path(root) / path) for path in sorted(selected)}
    if not isinstance(external, list):
        raise ValueError('invalid native external dependency closure')
    by_module = source_context(root) if context is None else context
    bindings = []
    for item in external:
        materials.require_keys(item, {'owner', 'module', 'path'}, 'native external module binding')
        key = (item['owner'], item['module'], item['path'])
        found = by_module.get(key)
        if found is None:
            raise ValueError('native external module is outside the resolved population: ' + repr(key))
        package, source = found
        bindings.append(dict(owner=item['owner'], module=item['module'], path=item['path'],
                             package=package['dir'], mode=source['mode'], sha256=source['sha256'],
                             ))
    return local, sorted(bindings, key=lambda item: (item['owner'], item['module'], item['path']))


def row_binding(rows, root, module_name, utility_path, *, template_inputs=None):
    if len(rows) != 1 or rows[0]['module'] != module_name:
        raise ValueError('native module binding mismatch')
    row = rows[0]
    public.validate_template_sources(rows, root, inputs=template_inputs)
    record = public.read_json(Path(utility_path).read_bytes())
    path = record['source_path']
    if row['source_path'] != path or row['source_sha256'] != 'sha256:' + public.digest(Path(root) / path):
        raise ValueError('native module source mismatch')
    obligations = record['utilities']
    if not obligations:
        if 'utility_refutation' in row:
            raise ValueError('unexpected utility evidence')
    else:
        utility = obligations[0]
        evidence = row.get('utility_refutation', {})
        for raw, field in [('claimGid', 'claim_gid'), ('claimSourcePath', 'claim_source_path'),
                           ('claimSourceSha256', 'claim_source_sha256'), ('resultGid', 'result_gid')]:
            if evidence.get(field) != utility[raw]:
                raise ValueError('native utility binding mismatch')


def module(root, name, source, utility_path, executable, output):
    root, source, output = Path(root), Path(source), Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.module.', dir=output.parent) as directory:
        directory = Path(directory)
        record = public.read_json(Path(utility_path).read_bytes())
        bindings, external_bindings = input_sources(root, utility_path,
            context=source_context(root, require_snapshot=True))
        utility = directory / 'utility.json'
        utility.write_bytes(materials.canonical_json(record['utilities']))
        spool = directory / 'spool'
        spool.mkdir()
        report = directory / public.RAW
        subprocess.run([str(executable), '--output', str(directory / 'spool.json'), '--material-spool', str(spool),
            '--utility-input', str(utility), name, record['source_path'], 'sha256:' + public.digest(source)], check=True, cwd=root)
        materials.compact(directory / 'spool.json', spool, report, root / 'lean-report-inputs.json')
        # Lake returns only canonically validated public facets. Generation is
        # private; the completed artifact gets its full validation at acceptance.
        rows = public.read_json(report.read_bytes())['modules']
        row_binding(rows, root, name, utility_path)
        artifact = directory / 'module.zip'
        public.write_origin(report, name, dict(public.production_origin(root, executable),
                                              input_sources=bindings, external_inputs=external_bindings))
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
        os.replace(artifact, output)
        activity('extract', 1)
        print(f'LEAN_INSPECTOR_EXTRACT module={name} declarations={len(rows[0]["declarations"])}')


def produce_batch(requests):
    requests = sorted(requests, key=lambda row: row[1])
    root = Path(requests[0][0])
    template_inputs = selection.Selection(root)
    executable = requests[0][4]
    origin = public.production_origin(root, executable)
    context = source_context(root, require_snapshot=True)
    if any(Path(row[0]) != root or row[4] != executable for row in requests):
        raise ValueError('mixed native batch owners')
    with tempfile.TemporaryDirectory(prefix='.inspection.', dir=state(root)) as directory:
        directory = Path(directory)
        spool = directory / 'spool'
        spool.mkdir()
        utilities = []
        triples = []
        bindings = {}
        for _, name, source, utility_path, _, output in requests:
            if name in bindings:
                raise ValueError('duplicate native batch module')
            record = public.read_json(Path(utility_path).read_bytes())
            utilities.extend(record['utilities'])
            triples.extend([name, record['source_path'], 'sha256:' + public.digest(source)])
            local_bindings, external_bindings = input_sources(root, utility_path, context=context)
            bindings[name] = (utility_path, Path(output), local_bindings, external_bindings)
        utility_file = directory / 'utility.json'
        utility_file.write_bytes(materials.canonical_json(utilities))
        arguments = ['--output', str(directory / 'spool.json'), '--material-spool', str(spool),
                     '--utility-input', str(utility_file), *triples]
        argument_file = directory / 'arguments.json'
        argument_file.write_text(json.dumps(arguments))
        with phase('native-inspect'):
            subprocess.run([executable, '--request-file', str(argument_file)], cwd=root, check=True)
        raw = public.read_json((directory / 'spool.json').read_bytes())
        if [row['module'] for row in raw['modules']] != sorted(bindings):
            raise ValueError('incomplete native inspection batch')
        for row in raw['modules']:
            name = row['module']
            utility_path, output, sources, external_bindings = bindings[name]
            row_dir = directory / name
            row_dir.mkdir()
            row_spool = row_dir / 'spool'
            row_spool.mkdir()
            for decl in row['declarations']:
                source = materials.regular_spool_file(spool, decl['material_file'])
                os.replace(source, row_spool / source.name)
            spool_report = row_dir / 'spool.json'
            spool_report.write_bytes(materials.canonical_json({'schema': materials.SPOOL_SCHEMA, 'modules': [row]}))
            report = row_dir / public.RAW
            materials.compact(spool_report, row_spool, report, root / 'lean-report-inputs.json')
            rows = public.read_json(report.read_bytes())['modules']
            row_binding(rows, root, name, utility_path, template_inputs=template_inputs)
            output.parent.mkdir(parents=True, exist_ok=True)
            artifact = row_dir / 'module.zip'
            public.write_origin(report, name, dict(origin, input_sources=sources,
                                                  external_inputs=external_bindings))
            public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
            os.replace(artifact, output)
        if list(spool.iterdir()):
            raise ValueError('unreferenced batch materials')
        activity('extract', len(requests))
        print(f'LEAN_INSPECTOR_EXTRACT modules={len(requests)} declarations={sum(len(row["declarations"]) for row in raw["modules"])}')


@phase('native-batch')
def batch(request_file, result_file):
    requests = public.read_json(Path(request_file).read_bytes())
    produce = [args for kind, args in requests if kind == 'produce']
    if produce:
        with phase('native-produce'):
            produce_batch(produce)
    statuses = []
    verified_materials = {}
    source_scopes = {}
    contexts = {}

    def template_inputs(root):
        root = Path(root).resolve()
        if root not in source_scopes:
            source_scopes[root] = selection.Selection(root)
        return source_scopes[root]

    def context(root):
        root = Path(root).resolve()
        if root not in contexts:
            contexts[root] = source_context(root)
        return contexts[root]

    # The canonical Lake batch asks for each module's validation followed by
    # aggregation of exactly those modules. The builder already performs that
    # same complete validation, so let its row results serve both demands.
    # Other request shapes retain the ordinary independent boundaries.
    if requests and requests[-1][0] == 'aggregate':
        root, output, *artifacts = requests[-1][1]
        config = public.read_json((state(root) / 'inputs.json').read_bytes())
        expected = [['validate', [root, 'module', root, name,
            str(state(root) / 'inputs' / (name + '.json')), artifact]]
            for name, artifact in zip(config['modules'], artifacts)]
        # Lake's FilePath retains /./ while pathlib renders the same lexical
        # path without it. Compare paths without resolving symlinks or '..'.
        same_requests = len(requests) == len(expected) + 1 and all(
            kind == wanted_kind and len(args) == len(wanted_args) and
            args[:4] == wanted_args[:4] and Path(args[4]) == Path(wanted_args[4]) and
            args[5:] == wanted_args[5:]
            for (kind, args), (wanted_kind, wanted_args) in zip(requests, expected))
        if expected and len(artifacts) == len(config['modules']) and same_requests:
            aggregate(root, output, artifacts, verified_materials=verified_materials,
                      template_inputs=template_inputs(root), row_statuses=statuses)
            statuses.append(int(any(statuses)))
            Path(result_file).write_text(json.dumps(statuses))
            return

    for kind, args in requests:
        if kind == 'produce':
            statuses.append(0)
        elif kind == 'validate':
            try:
                validate(*args[1:], verified_materials=verified_materials,
                         template_inputs=template_inputs(args[0]), context=context(args[0]))
                statuses.append(0)
            except ROW_ERRORS as error:
                print(f'LEAN_INSPECTOR_REJECT {error}', file=sys.stderr)
                statuses.append(1)
        elif kind == 'aggregate':
            if any(statuses):
                statuses.append(1)
            else:
                root, output, *artifacts = args
                aggregate(root, output, artifacts, verified_materials=verified_materials,
                          template_inputs=template_inputs(root))
                statuses.append(0)
        else:
            raise ValueError('unknown native batch operation')
    Path(result_file).write_text(json.dumps(statuses))


def aggregate(root, output, artifacts, verified_materials=None, *, template_inputs=None, row_statuses=None):
    root, output = Path(root), Path(output)
    if template_inputs is None:
        template_inputs = selection.Selection(root)
    config = public.read_json((state(root) / 'inputs.json').read_bytes())
    context = source_context(root)
    if len(artifacts) != len(config['modules']):
        raise ValueError('native aggregate membership mismatch')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.aggregate.', dir=output.parent) as directory, \
            tempfile.TemporaryFile(dir=output.parent) as material_spool:
        directory = Path(directory)
        material_offsets = {}
        rows = []
        origins = {}
        for name, artifact in zip(config['modules'], artifacts):
            with tempfile.TemporaryDirectory(prefix='row.', dir=directory) as row_dir:
                try:
                    report = public.unpack(artifact, row_dir, ROW_SUFFIXES)
                    current, origin = validate_module(report, root, name,
                        state(root) / 'inputs' / (name + '.json'),
                        verified_materials=verified_materials, template_inputs=template_inputs, context=context)
                    if origin['compatibility_sha256'] != config['coordinates']['producer']:
                        raise ValueError('native aggregate compatibility mismatch')
                except ROW_ERRORS as error:
                    if row_statuses is None:
                        raise
                    print(f'LEAN_INSPECTOR_REJECT {error}', file=sys.stderr)
                    row_statuses.append(1)
                    continue
                if row_statuses is not None:
                    row_statuses.append(0)
                origins[name] = origin
                rows.extend(current)
                with zipfile.ZipFile(public.member(report, '.materials.zip')) as archive:
                    for entry in archive.infolist():
                        with archive.open(entry) as reader:
                            if entry.filename in material_offsets:
                                offset, size = material_offsets[entry.filename]
                                material_spool.seek(offset)
                                seen = 0
                                for block in iter(lambda: reader.read(materials.BUFFER_BYTES), b''):
                                    seen += len(block)
                                    if seen > size or block != material_spool.read(len(block)):
                                        raise ValueError('statement material address collision')
                                if seen != size:
                                    raise ValueError('statement material address collision')
                            else:
                                material_spool.seek(0, os.SEEK_END)
                                offset = material_spool.tell()
                                shutil.copyfileobj(reader, material_spool, materials.BUFFER_BYTES)
                                material_offsets[entry.filename] = (offset, material_spool.tell() - offset)
        if row_statuses is not None and any(row_statuses):
            return
        report = directory / public.RAW
        report.write_bytes(materials.canonical_json({'modules': rows, 'schema': materials.REPORT_SCHEMA}))
        with zipfile.ZipFile(public.member(report, '.materials.zip'), 'w', compression=zipfile.ZIP_DEFLATED,
                             compresslevel=6, allowZip64=True) as archive:
            for name, (offset, size) in sorted(material_offsets.items()):
                info = zipfile.ZipInfo(name, materials.ARCHIVE_TIMESTAMP)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                material_spool.seek(offset)
                with archive.open(info, 'w') as writer:
                    remaining = size
                    while remaining:
                        block = material_spool.read(min(materials.BUFFER_BYTES, remaining))
                        if not block:
                            raise ValueError('truncated private material spool')
                        writer.write(block)
                        remaining -= len(block)
        public.write_sidecars(report, config['coordinates'], origins,
                              native_inputs=config.get('native_inputs'))
        # The native aggregate facet validates the completed bundle before
        # exposing it. Do not repeat that complete pass inside its builder.
        artifact = directory / 'report.zip'
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in public.SUFFIXES])
        os.replace(artifact, output)
        activity('aggregate', 1)
        print(f'LEAN_INSPECTOR_AGGREGATE modules={len(rows)} declarations={sum(len(row["declarations"]) for row in rows)}')


def validate_module(report, root, name, utility, *, verified_materials=None, template_inputs=None, context=None):
    rows = public.validate_rows(report, public.member(report, '.materials.zip'), verified_materials,
                                manifest=Path(root) / 'lean-report-inputs.json')
    row_binding(rows, root, name, utility, template_inputs=template_inputs)
    # prepare validated the manifest before any facet could accept an artifact.
    compatibility = (state(root) / 'compatibility').read_text(encoding='ascii').strip()
    origin = public.validate_origin(report, rows, compatibility)
    if 'external_inputs' not in origin:
        raise ValueError('missing native external row inputs')
    local_bindings, external_bindings = input_sources(root, utility, context=context)
    if origin['input_sources'] != local_bindings or origin.get('external_inputs', []) != external_bindings:
        raise ValueError('native dependency source binding mismatch')
    return rows, origin


def validate(kind, root, *args, verified_materials=None, template_inputs=None, context=None):
    if template_inputs is None:
        template_inputs = selection.Selection(root)
    with tempfile.TemporaryDirectory(prefix='.validate.', dir=state(root)) as directory:
        if kind == 'module':
            name, utility, artifact = args
            report = public.unpack(artifact, directory, ROW_SUFFIXES)
            validate_module(report, root, name, utility, verified_materials=verified_materials,
                            template_inputs=template_inputs, context=context)
        elif kind == 'report':
            report = public.unpack(args[0], directory)
            config = public.read_json((state(root) / 'inputs.json').read_bytes())
            rows = public.validate_bundle(report, config['coordinates'], root, verified_materials)
            if [row['module'] for row in rows] != config['modules']:
                raise ValueError('native aggregate membership mismatch')
            for row in rows:
                row_binding([row], root, row['module'], state(root) / 'inputs' / (row['module'] + '.json'),
                            template_inputs=template_inputs)
        else:
            raise ValueError('unknown native artifact kind')


def publish(root, destination):
    inputs = public.coordinates(root)
    with tempfile.TemporaryDirectory(prefix='.publish.', dir=state(root)) as directory:
        report = public.unpack(state(root) / 'report.zip', directory)
        activity_file = os.environ.get('STRATALINT_INSPECTOR_ACTIVITY')
        mode = None
        if activity_file:
            records = [public.read_json(line) for line in Path(activity_file).read_text().splitlines()]
            mode = 'produced' if records else 'cached'
            print(f'LEAN_INSPECTOR_WORK extracted_modules={sum(row["count"] for row in records if row["kind"] == "extract")} aggregates={sum(row["count"] for row in records if row["kind"] == "aggregate")}')
        public.publish(report, Path(destination), inputs, root, mode=mode)
    print(f'RAW_LEAN_REPORT path={destination} sha256={public.digest(destination)}')


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == 'prepare':
        if len(sys.argv) not in (3, 5) or (len(sys.argv) == 5 and sys.argv[3] != '--lake-inputs'):
            raise ValueError('prepare expects ROOT [--lake-inputs FILE]')
        return prepare(sys.argv[2], sys.argv[4] if len(sys.argv) == 5 else None)
    actions = {'module': module, 'aggregate': lambda root, output, *paths: aggregate(root, output, paths),
               'validate': validate, 'publish': publish, 'batch': batch}
    if len(sys.argv) < 2 or sys.argv[1] not in actions:
        raise ValueError('expected prepare, module, aggregate, validate, or publish')
    actions[sys.argv[1]](*sys.argv[2:])


if __name__ == '__main__':
    try:
        main()
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print(f'lean-inspector-native: {error}', file=sys.stderr)
        raise SystemExit(1)
