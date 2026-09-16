#!/usr/bin/env python3
"""Inspector-owned canonical bundle validation and private publication.

Optional artifacts are validated before use. This module has no reuse index,
source planner, remote transport, or persistent store.
"""
from __future__ import annotations

import argparse
from contextlib import nullcontext
from functools import lru_cache
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import tempfile
import zipfile

import materials

_selection_spec = importlib.util.spec_from_file_location('report_selection',
    Path(__file__).resolve().parent.parent / 'scripts/report/lean-report-selection.py')
selection = importlib.util.module_from_spec(_selection_spec)
_selection_spec.loader.exec_module(selection)

# This Selection module is private to the inspector. Only the pure grammar
# computation is memoized; safe_file still checks every current path component.
_compile_glob = selection.compile_glob
_compiled_glob = lru_cache(maxsize=16384)(_compile_glob)


def compile_glob(pattern, location):
    if not isinstance(pattern, str) or not isinstance(location, str):
        return _compile_glob(pattern, location)
    return _compiled_glob(pattern, location)


selection.compile_glob = compile_glob

RAW = 'raw-lean-report.json'
SUFFIXES = ('', '.sha256', '.input.attestation', '.provenance.json', '.materials.zip')
SHA = re.compile(r'sha256:[0-9a-f]{64}')
HEX = re.compile(r'[0-9a-f]{64}')
KINDS = {'axiom', 'def', 'theorem', 'opaque', 'quotient', 'constructor', 'recursor', 'inductive'}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON field: {key}')
        result[key] = value
    return result


def read_json(data):
    return json.loads(data, object_pairs_hook=unique_object)


def member(report, suffix):
    return Path(str(report) + suffix)


def open_zip_member(archive, info):
    # CPython raises RuntimeError before decoding when an optional module is
    # absent. Reject that artifact condition without catching program failures.
    for method, decoder, name in ((zipfile.ZIP_DEFLATED, zipfile.zlib, 'DEFLATE'),
            (zipfile.ZIP_BZIP2, zipfile.bz2, 'BZIP2'), (zipfile.ZIP_LZMA, zipfile.lzma, 'LZMA')):
        if info.compress_type == method and decoder is None:
            raise ValueError('unavailable ZIP decoder: ' + name)
    return archive.open(info)


def digest(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as source:
        for block in iter(lambda: source.read(materials.BUFFER_BYTES), b''):
            result.update(block)
    return result.hexdigest()


def coordinates(repository):
    helper = Path(repository) / 'tools/scripts/report/lean-report-input.sh'
    lake = Path(repository) / '.lake'
    # Pre-ensure validation must leave an absent .lake eligible for whole-tree
    # donor seeding. Existing trees keep their reusable input memo.
    with (nullcontext(str(lake / 'lean-input-memo')) if lake.exists() else
            tempfile.TemporaryDirectory(prefix='lean-report-input-memo.', dir=os.environ.get('TMPDIR'))) as memo:
        env = dict(os.environ, STRATALINT_LEAN_INPUT_MEMO_ROOT=memo)
        values = subprocess.check_output([str(helper), 'address', '--repository', str(repository)], text=True, env=env).strip().split(' ')
    if len(values) != 4 or any(not HEX.fullmatch(value) for value in values):
        raise ValueError('malformed repository input address')
    repository_id, producer, sources, config = values
    pair = subprocess.check_output([str(helper), 'coordinates', producer, producer, sources, config], text=True).strip().split(' ')
    if len(pair) != 2 or pair[1] != repository_id or not HEX.fullmatch(pair[0]):
        raise ValueError('malformed report input coordinates')
    return dict(repository=repository_id, producer=producer, sources=sources, config=config, input=pair[0])


def production_origin(repository, executable):
    """Actual generation evidence, never a Lake report dependency or currentness test."""
    inputs = selection.Selection(repository)
    inputs.validate('lean-report')
    fingerprint = hashlib.sha256()
    for path in inputs.producer_paths('lean-report'):
        sha = (hashlib.sha256(inputs.projection('lean-report').encode('ascii')).hexdigest()
               if path == selection.MANIFEST else digest(inputs.safe_file(path)))
        fingerprint.update(path.encode('utf-8') + b'\0' + sha.encode('ascii') + b'\n')
    return dict(compatibility_sha256=inputs.compatibility(), producer_sources_sha256=fingerprint.hexdigest(),
                inspector_executable_sha256=digest(executable))


def write_origin(report, name, origin):
    record = dict(origin, module=name, report_sha256=digest(report))
    member(report, '.provenance.json').write_bytes(materials.canonical_json(record))


def check_origin(origin, row, compatibility):
    materials.require_keys(origin, {'module', 'report_sha256', 'compatibility_sha256',
        'producer_sources_sha256', 'inspector_executable_sha256', 'input_sources'}, 'module production origin')
    bindings = origin['input_sources']
    if (not isinstance(bindings, dict) or bindings.get(row['source_path']) != row['source_sha256'][7:]
            or any(not isinstance(sha, str) or not HEX.fullmatch(sha) for sha in bindings.values())):
        raise ValueError('module dependency source binding mismatch')
    for path in bindings:
        selection.compile_glob(path, 'dependency source binding')
    if (origin['module'] != row['module'] or origin['compatibility_sha256'] != compatibility
            or any(not isinstance(origin[k], str) or not HEX.fullmatch(origin[k]) for k in
                   ('report_sha256', 'compatibility_sha256', 'producer_sources_sha256', 'inspector_executable_sha256'))
            or origin['report_sha256'] != hashlib.sha256(materials.canonical_json(
                dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest()):
        raise ValueError('invalid or incompatible module production origin')


def validate_origin(report, rows, compatibility):
    if len(rows) != 1:
        raise ValueError('module origin requires exactly one row')
    origin = read_json(member(report, '.provenance.json').read_bytes())
    check_origin(origin, rows[0], compatibility)
    return origin


def write_sidecars(report, inputs, origins, mode='produced'):
    sha = digest(report)
    member(report, '.sha256').write_text(f'{sha}  {report.name}\n', encoding='ascii')
    member(report, '.input.attestation').write_text(
        'schema=stratalint-lean-report-input-attestation-v1\n'
        f'repository_input_sha256={inputs["repository"]}\nproducer_sha256={inputs["producer"]}\nreport_sha256={sha}\n', encoding='ascii')
    provenance = dict(schema='stratalint-lean-report-provenance-v2', side='candidate', mode=mode,
        source_side='candidate', input_address='sha256:' + inputs['input'], producer_sha256=inputs['producer'],
        repository_inspector_sha256=inputs['producer'], lean_sources_sha256=inputs['sources'],
        lean_config_sha256=inputs['config'], report_sha256=sha, module_origins=origins)
    member(report, '.provenance.json').write_text(json.dumps(provenance, separators=(',', ':')) + '\n', encoding='utf-8')


def validate_rows(report, archive_path, verified_materials=None):
    data = Path(report).read_bytes()
    root = read_json(data)
    materials.require_keys(root, {'modules', 'schema'}, 'report')
    if root['schema'] != materials.REPORT_SCHEMA or not isinstance(root['modules'], list):
        raise ValueError('invalid raw report schema')
    if data != materials.canonical_json(root):
        raise ValueError('noncanonical raw report bytes')
    previous = None
    paths = set()
    references = {}
    for row in root['modules']:
        keys = {'module', 'source_path', 'source_sha256', 'imports', 'declarations'}
        keys.update(key for key in ('information_registration_errors', 'information_templates', 'utility_refutation') if key in row)
        materials.require_keys(row, keys, 'module')
        name, path, sha = row['module'], row['source_path'], row['source_sha256']
        if (not isinstance(name, str) or not name or previous is not None and name <= previous
                or not isinstance(path, str) or not path or path in paths
                or not isinstance(sha, str) or not SHA.fullmatch(sha)):
            raise ValueError('invalid or duplicate module/source binding')
        previous = name
        paths.add(path)
        materials.require_sorted_strings(row['imports'], 'imports')
        if 'information_registration_errors' in row:
            materials.require_sorted_strings(row['information_registration_errors'], 'registration errors')
        if 'information_templates' in row:
            materials.validate_template_evidence(row['information_templates'])
        if 'utility_refutation' in row:
            evidence = materials.require_keys(row['utility_refutation'], {'claim_gid', 'claim_source_path',
                'claim_source_sha256', 'result_gid', 'is_closed_negation'}, 'utility refutation')
            if (any(not isinstance(evidence[k], str) or not evidence[k] for k in ('claim_gid', 'claim_source_path', 'result_gid'))
                    or not isinstance(evidence['claim_source_sha256'], str)
                    or not SHA.fullmatch(evidence['claim_source_sha256']) or type(evidence['is_closed_negation']) is not bool):
                raise ValueError('invalid typed refutation')
        if not isinstance(row['declarations'], list):
            raise ValueError('invalid declarations')
        previous_key = None
        for decl in row['declarations']:
            materials.require_keys(decl, {'axioms', 'include_in_statement', 'kind', 'name', 'name_key', 'statement_id', 'type_sha256'}, 'declaration')
            key = decl['name_key']
            if (not isinstance(key, str) or not key or previous_key is not None and key <= previous_key
                    or not isinstance(decl['name'], str) or not decl['name'] or decl['kind'] not in KINDS
                    or type(decl['include_in_statement']) is not bool
                    or any(not isinstance(decl[k], str) or not SHA.fullmatch(decl[k]) for k in ('statement_id', 'type_sha256'))):
                raise ValueError('invalid or duplicate declaration')
            previous_key = key
            materials.require_sorted_strings(decl['axioms'], 'axioms')
            references.setdefault('sha256/' + decl['type_sha256'][7:], []).append((row, decl))
    with zipfile.ZipFile(archive_path) as archive:
        names = archive.namelist()
        if len(names) != len(references) or set(names) != set(references):
            raise ValueError('duplicate, missing, or unreferenced material')
        for name in names:
            info = archive.getinfo(name)
            if info.is_dir() or stat.S_ISLNK(info.external_attr >> 16):
                raise ValueError('nonregular material')
            if info.flag_bits & 1:
                raise ValueError('encrypted material')
            for row, decl in references[name]:
                key = (row['source_path'], decl['kind'], decl['name_key'], decl['type_sha256'])
                with open_zip_member(archive, info) as source:
                    if verified_materials is not None and key in verified_materials:
                        # Invocation-local reuse of the expensive canonical
                        # statement encoding. Always read/CRC-check/hash the
                        # actual bytes again; an archive address is no proof.
                        materials.verify_material(source, decl['type_sha256'])
                        actual = (decl['type_sha256'], verified_materials[key])
                    else:
                        actual = materials.material_identities(source, row['source_path'], decl['kind'], decl['name_key'])
                if actual != (decl['type_sha256'], decl['statement_id']):
                    raise ValueError('material or declaration identity mismatch')
                if verified_materials is not None:
                    verified_materials[key] = actual[1]
    return root['modules']


def validate_sources(rows, repository):
    inputs = selection.Selection(repository)
    modules = inputs.modules()
    if [row['module'] for row in rows] != sorted(modules):
        raise ValueError('report source membership mismatch')
    for row in rows:
        path = modules[row['module']]
        if row['source_path'] != path or row['source_sha256'] != 'sha256:' + digest(inputs.safe_file(path)):
            raise ValueError('report source binding mismatch')
        evidence = row.get('utility_refutation')
        if evidence and evidence['claim_source_sha256'] != 'sha256:' + digest(inputs.safe_file(evidence['claim_source_path'])):
            raise ValueError('report claim source binding mismatch')
    validate_template_sources(rows, repository, inputs=inputs)


def validate_template_sources(rows, repository, *, inputs=None):
    """Reject stale binding inputs before native reuse or final publication.

    Their paths are emitted by the checked driver. This checks byte binding;
    the strict C# consumer still checks the complete evidence semantics.
    """
    # Selection expands the report scope. A native batch shares that immutable
    # scope description; path checks and byte digests remain fresh per call.
    if inputs is None:
        inputs = selection.Selection(repository)
    elif inputs.root != Path(repository).resolve():
        raise ValueError('declared-template input owner mismatch')
    observed = {}
    for row in rows:
        evidence = row.get('information_templates')
        if evidence is None:
            continue
        materials.validate_template_evidence(evidence)
        previous = None
        for source in evidence['inputs']:
            materials.require_keys(source, {'path', 'sha256'}, 'declared-template input')
            path, sha = source['path'], source['sha256']
            if (not isinstance(path, str) or not path or previous is not None and path <= previous
                    or not isinstance(sha, str) or not re.fullmatch(r'[0-9a-f]{64}', sha)):
                raise ValueError('malformed declared-template input binding')
            previous = path
            if path not in observed:
                observed[path] = digest(inputs.safe_file(path))
            if observed[path] != sha:
                raise ValueError('stale declared-template input binding: ' + path)


def validate_dependency_sources(origins, repository):
    inputs = selection.Selection(repository)
    allowed = set(inputs.dependency_sources())
    observed = {}
    for origin in origins.values():
        for path, sha in origin['input_sources'].items():
            if path not in allowed:
                raise ValueError('unregistered dependency source binding: ' + path)
            if path not in observed:
                observed[path] = digest(inputs.safe_file(path))
            if observed[path] != sha:
                raise ValueError('stale dependency source binding: ' + path)


def verify_inputs(report, repository):
    """Input-only verification; the full material validator remains separate."""
    rows = read_json(Path(report).read_bytes())['modules']
    provenance = read_json(member(report, '.provenance.json').read_bytes())
    origins = provenance['module_origins']
    materials.require_keys(origins, {row['module'] for row in rows}, 'aggregate production origins')
    compatibility = selection.Selection(repository).compatibility()
    for row in rows:
        check_origin(origins[row['module']], row, compatibility)
    validate_sources(rows, repository)
    validate_dependency_sources(origins, repository)


def _require_bundle_files(report):
    for suffix in SUFFIXES:
        path = member(report, suffix)
        if path.is_symlink() or not path.is_file() or not path.stat().st_size:
            raise ValueError(f'missing bundle member: {path.name}')


def validate_bundle(report, expected=None, repository=None, verified_materials=None):
    report = Path(report)
    _require_bundle_files(report)
    sha = digest(report)
    if member(report, '.sha256').read_text(encoding='ascii') != f'{sha}  {report.name}\n':
        raise ValueError('report SHA mismatch')
    provenance = read_json(member(report, '.provenance.json').read_bytes())
    materials.require_keys(provenance, {'schema', 'side', 'mode', 'source_side', 'input_address', 'producer_sha256',
        'repository_inspector_sha256', 'lean_sources_sha256', 'lean_config_sha256', 'report_sha256', 'module_origins'}, 'provenance')
    if (provenance['schema'] != 'stratalint-lean-report-provenance-v2' or provenance['side'] != 'candidate'
            or provenance['source_side'] != 'candidate' or provenance['mode'] not in ('produced', 'cached')
            or provenance['report_sha256'] != sha or not SHA.fullmatch(provenance['input_address'])
            or any(not HEX.fullmatch(provenance[k]) for k in ('producer_sha256', 'repository_inspector_sha256',
                'lean_sources_sha256', 'lean_config_sha256', 'report_sha256'))):
        raise ValueError('invalid provenance')
    lines = member(report, '.input.attestation').read_text(encoding='ascii').splitlines()
    if (len(lines) != 4 or lines[0] != 'schema=stratalint-lean-report-input-attestation-v1'
            or not re.fullmatch('repository_input_sha256=[0-9a-f]{64}', lines[1])
            or lines[2] != 'producer_sha256=' + provenance['producer_sha256'] or lines[3] != 'report_sha256=' + sha):
        raise ValueError('invalid input attestation')
    helper = Path(__file__).resolve().parent.parent / 'scripts/report/lean-report-input.sh'
    coordinates = subprocess.check_output([str(helper), 'coordinates',
        *(provenance[k] for k in ('producer_sha256', 'repository_inspector_sha256',
                                  'lean_sources_sha256', 'lean_config_sha256'))], text=True).strip().split(' ')
    if coordinates != [provenance['input_address'][7:], lines[1].split('=', 1)[1]]:
        raise ValueError('bundle input coordinate mismatch')
    if expected is not None:
        wanted = {'input_address': 'sha256:' + expected['input'], 'producer_sha256': expected['producer'],
            'repository_inspector_sha256': expected['producer'], 'lean_sources_sha256': expected['sources'],
            'lean_config_sha256': expected['config']}
        if any(provenance[k] != v for k, v in wanted.items()) or lines[1] != 'repository_input_sha256=' + expected['repository']:
            raise ValueError('stale input/provenance')
    rows = validate_rows(report, member(report, '.materials.zip'), verified_materials)
    origins = provenance['module_origins']
    materials.require_keys(origins, {row['module'] for row in rows}, 'aggregate production origins')
    for row in rows:
        check_origin(origins[row['module']], row, provenance['producer_sha256'])
    if repository is not None:
        validate_sources(rows, repository)
        validate_dependency_sources(origins, repository)
    return rows


def zip_files(destination, paths):
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_STORED, allowZip64=True) as archive:
        for name, source in paths:
            info = zipfile.ZipInfo(name, materials.ARCHIVE_TIMESTAMP)
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            with Path(source).open('rb') as reader, archive.open(info, 'w', force_zip64=Path(source).stat().st_size >= zipfile.ZIP64_LIMIT) as writer:
                shutil.copyfileobj(reader, writer, materials.BUFFER_BYTES)


def unpack(artifact, directory, suffixes=SUFFIXES):
    expected = {RAW + suffix for suffix in suffixes}
    with zipfile.ZipFile(artifact) as archive:
        if len(archive.namelist()) != len(expected) or set(archive.namelist()) != expected:
            raise ValueError('invalid native artifact members')
        for name in sorted(expected):
            info = archive.getinfo(name)
            if info.is_dir() or stat.S_IFMT(info.external_attr >> 16) not in (0, stat.S_IFREG):
                raise ValueError('nonregular native artifact member')
            if info.flag_bits & 1:
                raise ValueError('encrypted native artifact member')
            with open_zip_member(archive, info) as reader, (Path(directory) / name).open('wb') as writer:
                shutil.copyfileobj(reader, writer, materials.BUFFER_BYTES)
    return Path(directory) / RAW


def publish(report, destination, expected, repository=None, *, mode=None):
    report, destination = Path(report), Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    _require_bundle_files(report)
    with tempfile.TemporaryDirectory(prefix='.lean-report.', dir=destination.parent) as directory:
        # Keep the incoming basename and every sidecar byte until the complete
        # private snapshot has passed canonical and current repository checks.
        staged = Path(directory) / 'bundle' / report.name
        staged.parent.mkdir()
        for suffix in SUFFIXES:
            shutil.copyfile(member(report, suffix), member(staged, suffix))
        accepted = {suffix: digest(member(staged, suffix)) for suffix in SUFFIXES}
        validate_bundle(staged, expected, repository)
        if any(digest(member(staged, suffix)) != sha for suffix, sha in accepted.items()):
            raise ValueError('publication snapshot changed during validation')

        updates = {'.sha256': f'{accepted[""]}  {destination.name}\n'.encode('ascii')}
        if mode is not None:
            if mode not in ('produced', 'cached'):
                raise ValueError('invalid publication mode')
            # Only the publication mode changes; actual module origins survive
            # reuse, including aggregates with mixed production fingerprints.
            provenance = read_json(member(staged, '.provenance.json').read_bytes())
            provenance['mode'] = mode
            updates['.provenance.json'] = (json.dumps(provenance, separators=(',', ':')) + '\n').encode('utf-8')
        for suffix, data in updates.items():
            member(staged, suffix).write_bytes(data)
            accepted[suffix] = hashlib.sha256(data).hexdigest()
        _require_bundle_files(staged)
        if any(digest(member(staged, suffix)) != sha for suffix, sha in accepted.items()):
            raise ValueError('publication snapshot changed after validation')
        previous = Path(directory) / 'previous'
        previous.mkdir()
        backups = {}
        for suffix in SUFFIXES:
            path = member(destination, suffix)
            backup = previous / (destination.name + suffix)
            if os.path.lexists(path):
                # Replacements never write through these links. Keep the old
                # bytes available without copying a second material archive.
                os.link(path, backup, follow_symlinks=False)
                backups[suffix] = backup
        # Publish the validated report last. Concurrent readers fail closed on a
        # transitional sidecar mismatch; they can never accept a mixed bundle.
        replaced = []
        try:
            for suffix in (*SUFFIXES[1:], ''):
                os.replace(member(staged, suffix), member(destination, suffix))
                replaced.append(suffix)
        except BaseException:
            for suffix in reversed(replaced):
                if suffix in backups:
                    os.replace(backups[suffix], member(destination, suffix))
                else:
                    member(destination, suffix).unlink()
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    validate = sub.add_parser('validate')
    validate.add_argument('report', type=Path)
    validate.add_argument('--repository', type=Path)
    verify = sub.add_parser('verify-inputs')
    verify.add_argument('report', type=Path)
    verify.add_argument('--repository', required=True, type=Path)
    stage = sub.add_parser('stage')
    stage.add_argument('--bundle', required=True, type=Path)
    stage.add_argument('--staging-directory', required=True, type=Path)
    stage.add_argument('--repository', required=True, type=Path)
    args = parser.parse_args()
    if args.command == 'verify-inputs':
        verify_inputs(args.report, args.repository)
        return
    expected = coordinates(args.repository) if args.repository else None
    if args.command == 'validate':
        validate_bundle(args.report, expected, args.repository)
    else:
        output = args.staging_directory / RAW
        publish(args.bundle, output, expected, args.repository)
        print(output)


if __name__ == '__main__':
    try:
        main()
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print(f'lean-inspector-publication: {error}', file=__import__('sys').stderr)
        raise SystemExit(1)
