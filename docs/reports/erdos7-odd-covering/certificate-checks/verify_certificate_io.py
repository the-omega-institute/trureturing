#!/usr/bin/env python3
"""Independent compressed-certificate positive/negative and replay checks."""
import argparse
import base64
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import zlib

sys.dont_write_bytecode = True
KIND = 'value-zlib-base85'
FORMAT = 'erdos7-semantic-certificate-v1'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2) + '\n').encode('utf-8')


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate key')
        result[key] = value
    return result


def parse(raw):
    return json.loads(raw.decode('utf-8'), object_pairs_hook=unique)


def envelope(raw, compressed=None):
    return {'byte_length': len(raw), 'sha256': digest(raw),
            'data': base64.b85encode(zlib.compress(raw) if compressed is None else compressed).decode('ascii')}


def independent_read(path):
    """Independent physical DAG replay, including exact compressed-leaf bytes."""
    raw = path.read_bytes()
    doc = parse(raw)
    if not isinstance(doc, dict) or 'certificate_format' not in doc:
        return raw, 0
    require(set(doc) == {'certificate_format', 'logical_sha256', 'parts_directory', 'root'}, 'manifest fields')
    require(doc['certificate_format'] == FORMAT, 'format')
    require(doc['parts_directory'] == path.stem + '.parts', 'parts directory')
    base = path.with_name(path.stem + '.parts')
    require(not base.is_symlink(), 'symlink root')
    visited = set()
    compressed_count = 0

    def walk(ref):
        nonlocal compressed_count
        if ref.get('kind') == 'inline':
            require(set(ref) == {'kind', 'value'}, 'inline fields')
            return ref['value']
        require(set(ref) == {'kind', 'path', 'sha256'}, 'reference fields')
        name = ref['path']
        require(isinstance(name, str), 'path type')
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts and relative.as_posix() == name
                and relative.suffix == '.json', 'unsafe path')
        require(name not in visited, 'repeated part')
        visited.add(name)
        target = base / relative
        require(target.resolve().is_relative_to(base.resolve()), 'escaped part')
        require(not any(base.joinpath(*relative.parts[:n]).is_symlink() for n in range(1, len(relative.parts) + 1)), 'symlink part')
        payload = target.read_bytes()
        require(digest(payload) == ref['sha256'], 'physical hash')
        value = parse(payload)
        kind = ref['kind']
        if kind == KIND:
            compressed_count += 1
            require(isinstance(value, dict) and set(value) == {'byte_length', 'sha256', 'data'}, 'codec fields')
            n = value['byte_length']
            require(type(n) is int and 0 <= n <= 16 * 1024 * 1024, 'codec length')
            require(isinstance(value['data'], str), 'codec data')
            encoded = value['data'].encode('ascii')
            packed = base64.b85decode(encoded)
            require(base64.b85encode(packed) == encoded, 'base85 canonical form')
            decoder = zlib.decompressobj()
            decoded = decoder.decompress(packed, n + 1)
            require(len(decoded) == n and decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail,
                    'compression framing')
            require(digest(decoded) == value['sha256'], 'decoded hash')
            return parse(decoded)
        if kind == 'value':
            return value
        if kind == 'object':
            require(isinstance(value, dict), 'object type')
            return {key: walk(child) for key, child in value.items()}
        if kind == 'singleton':
            require(set(value) == {'item'}, 'singleton fields')
            return [walk(value['item'])]
        require(kind == 'array' and set(value) == {'length', 'chunks'}, 'array kind/fields')
        require(type(value['length']) is int and value['length'] >= 0 and isinstance(value['chunks'], list), 'array declaration')
        rows = []
        for chunk in value['chunks']:
            require(set(chunk) == {'start', 'stop', 'part'}, 'chunk fields')
            begin, end = chunk['start'], chunk['stop']
            require(type(begin) is int and type(end) is int and begin == len(rows) and end > begin, 'chunk interval')
            part = walk(chunk['part'])
            require(isinstance(part, list) and len(part) == end - begin, 'chunk length')
            rows.extend(part)
        require(len(rows) == value['length'], 'array length')
        return rows

    result = encode(walk(doc['root']))
    require(visited == {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}, 'part inventory')
    require(digest(result) == doc['logical_sha256'], 'logical hash')
    return result, compressed_count


class Fixture:
    def __init__(self, directory, name, logical):
        self.path = directory / (name + '.json')
        self.parts = directory / (name + '.parts')
        self.parts.mkdir()
        self.logical = encode(logical)

    def part(self, name, value, kind='value', raw=None):
        payload = encode(value) if raw is None else raw
        target = self.parts / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
        return {'path': name, 'sha256': digest(payload), 'kind': kind}

    def finish(self, ref):
        self.path.write_bytes(encode({'certificate_format': FORMAT, 'logical_sha256': digest(self.logical),
                                     'parts_directory': self.parts.name, 'root': ref}))
        return self.path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repository', type=Path, required=True)
    parser.add_argument('--replay-all', action='store_true')
    parser.add_argument('--originals', type=Path)
    args = parser.parse_args()
    source = args.repository / 'docs/reports/erdos7-odd-covering/certificate_io.py'
    spec = importlib.util.spec_from_file_location('certificate_io_under_test', source)
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    results = []

    def test(name, run):
        try:
            detail = run()
            results.append({'test': name, 'status': 'passed', 'detail': detail})
        except Exception as error:
            results.append({'test': name, 'status': 'failed', 'error': type(error).__name__ + ': ' + str(error)})
        print(json.dumps(results[-1]), flush=True)

    def accepted(path, expected):
        actual = io.read_artifact_bytes(path)
        require(actual == expected, 'production reader changed logical bytes')
        separate, count = independent_read(path)
        require(separate == expected, 'independent reader changed logical bytes')
        return {'logical_sha256': digest(actual), 'compressed_parts': count}

    def rejected(path):
        try:
            io.read_artifact_bytes(path)
        except Exception as error:
            return {'rejection': type(error).__name__ + ': ' + str(error)}
        raise ValueError('malformed certificate was accepted')

    with tempfile.TemporaryDirectory(prefix='certificate-codec-independent-') as scratch:
        root = Path(scratch)
        logical = {'rational': '17/19', 'rows': [[1, 2], [3, 4]], 'unicode': '\u03c6'}
        canonical = encode(logical)
        plain = root / 'plain.json'
        plain.write_bytes(canonical)
        test('legacy-plain', lambda: accepted(plain, canonical))
        for label, kind in [('legacy-part', 'value'), ('compressed-part', KIND)]:
            fixture = Fixture(root, label, logical)
            ref = fixture.part('content.json', envelope(canonical) if kind == KIND else logical, kind)
            test(label, lambda f=fixture, r=ref: accepted(f.finish(r), f.logical))
        mixed_value = {'rows': [logical, 9], 'legacy': {'kind': KIND, 'data': 'ordinary-user-data'}, 'inline': True}
        mixed = Fixture(root, 'mixed-nested', mixed_value)
        compressed = mixed.part('compressed.json', envelope(encode([logical])), KIND)
        last = mixed.part('last.json', [9])
        sequence = mixed.part('array.json', {'length': 2, 'chunks': [
            {'start': 0, 'stop': 1, 'part': compressed}, {'start': 1, 'stop': 2, 'part': last}]}, 'array')
        legacy = mixed.part('legacy.json', mixed_value['legacy'])
        mixed_root = mixed.part('content.json', {'rows': sequence, 'legacy': legacy, 'inline': {'kind': 'inline', 'value': True}}, 'object')
        test('mixed-nested', lambda: accepted(mixed.finish(mixed_root), mixed.logical))

        bad = {}
        def altered(name, **changes):
            bad[name] = {**envelope(canonical), **changes}
        altered('inner-hash', sha256='0' * 64)
        altered('short-length', byte_length=len(canonical) - 1)
        altered('long-length', byte_length=len(canonical) + 1)
        altered('bool-length', byte_length=True)
        altered('negative-length', byte_length=-1)
        altered('float-length', byte_length=float(len(canonical)))
        altered('string-length', byte_length=str(len(canonical)))
        altered('extra-field', unexpected='field')
        altered('data-type', data=[1, 2])
        altered('non-ascii', data='\u03c6')
        altered('bad-base85', data='abc~\n')
        altered('noncanonical-base85', data='0')
        packed = zlib.compress(canonical)
        for label, stream in [('truncated', packed[:-1]), ('trailing', packed + b'!'), ('concatenated', packed + packed),
                              ('gzip', zlib.compress(canonical, wbits=31)), ('raw-deflate', zlib.compress(canonical, wbits=-15))]:
            bad[label] = envelope(canonical, stream)
        bad['duplicate-decoded-key'] = envelope(b'{"rational":"wrong","rational":"17/19","rows":[[1,2],[3,4]],"unicode":"\\u03c6"}')
        bad['invalid-decoded-utf8'] = envelope(b'"\xff"')
        bad['invalid-decoded-json'] = envelope(b'{broken}')
        bad['logical-mutation'] = envelope(encode({'wrong': 'valid new JSON with valid inner/outer hashes'}))
        bad['bounded-expansion'] = {**envelope(b' ' * 1000000), 'byte_length': 8}
        for label, value in bad.items():
            fixture = Fixture(root, 'bad-' + label, logical)
            ref = fixture.part('content.json', value, KIND)
            test(label, lambda f=fixture, r=ref: rejected(f.finish(r)))
        for label in ['physical-hash', 'root-logical-hash', 'missing-part', 'unreferenced-part', 'symlink-part', 'escaped-part', 'unknown-kind']:
            fixture = Fixture(root, 'bad-' + label, logical)
            ref = fixture.part('content.json', envelope(canonical), KIND)
            if label == 'physical-hash': ref['sha256'] = '0' * 64
            if label == 'root-logical-hash': fixture.logical = b'changed logical root'
            if label == 'missing-part': (fixture.parts / 'content.json').unlink()
            if label == 'unreferenced-part': fixture.part('unused.json', [])
            if label == 'symlink-part':
                (fixture.parts / 'content.json').rename(fixture.parts / 'target.json')
                (fixture.parts / 'content.json').symlink_to('target.json')
            if label == 'escaped-part': ref['path'] = '../plain.json'
            if label == 'unknown-kind': ref['kind'] = 'value-zlib-base85-unknown'
            test(label, lambda f=fixture, r=ref: rejected(f.finish(r)))
        repeated = Fixture(root, 'bad-duplicate-part', {'a': logical, 'b': logical})
        ref = repeated.part('child.json', envelope(canonical), KIND)
        refs = repeated.part('content.json', {'a': ref, 'b': ref}, 'object')
        test('duplicate-part', lambda: rejected(repeated.finish(refs)))

        def writer_roundtrip_and_rollback():
            target = root / 'writer.json'
            initial = encode({'payload': ['abc0123456789' * 400 for _ in range(60)], 'rows': list(range(1100))})
            io.write_certificate_text(target, initial.decode())
            accepted(target, initial)
            _, count = independent_read(target)
            require(count > 0, 'writer did not produce compressed value')
            directory = target.with_name(target.stem + '.parts')
            before = {str(p.relative_to(root)): p.read_bytes() for p in [target, *directory.rglob('*')] if p.is_file()}
            original = io.os.replace
            injected = False
            def fail_manifest(src, dst):
                nonlocal injected
                if Path(dst) == target and not injected:
                    injected = True
                    raise OSError('independent injected manifest commit failure')
                return original(src, dst)
            io.os.replace = fail_manifest
            revised = encode({'payload': ['changed-payload' * 400 for _ in range(60)], 'rows': list(range(1101))})
            try:
                try:
                    io.write_certificate_text(target, revised.decode())
                except OSError as error:
                    require(str(error) == 'independent injected manifest commit failure', 'unexpected writer failure')
                else:
                    raise ValueError('injected manifest failure did not propagate')
            finally:
                io.os.replace = original
            require(injected, 'rollback injection was not reached')
            after = {str(p.relative_to(root)): p.read_bytes() for p in [target, *directory.rglob('*')] if p.is_file()}
            require(before == after, 'rollback altered old physical certificate')
            require(not list(root.glob('.writer-write-*')), 'writer left a staging directory')
            accepted(target, initial)
            io.write_certificate_text(target, revised.decode())
            accepted(target, revised)
            return {'compressed_parts': count, 'old_logical_sha256': digest(initial), 'new_logical_sha256': digest(revised)}
        test('writer-roundtrip-manifest-failure-rollback', writer_roundtrip_and_rollback)

        def declared_bound_before_decode():
            limit = 16 * 1024 * 1024
            require(io.MAX_COMPRESSED_VALUE_BYTES == limit, 'missing fixed codec bound')
            fixture = Fixture(root, 'oversized-declaration', logical)
            ref = fixture.part('content.json', {**envelope(canonical), 'byte_length': limit + 1}, KIND)
            path = fixture.finish(ref)
            original = io.b85decode
            calls = 0
            def touched(data):
                nonlocal calls
                calls += 1
                return original(data)
            io.b85decode = touched
            try:
                result = rejected(path)
                require(calls == 0, 'oversized declaration reached base85 decoder')
                require('byte length' in result['rejection'], 'wrong oversized rejection')
            finally:
                io.b85decode = original
            return {'limit': limit, 'base85_calls': calls}
        test('fixed-size-bound-before-base85', declared_bound_before_decode)

        def oversized_writer_fallback():
            limit = 16 * 1024 * 1024
            target = root / 'oversized-writer.json'
            content = {'payload': ['a' * 280000 for _ in range(61)], 'rows': list(range(1100))}
            expected = encode(content)
            require(len(encode(content['payload'])) > limit, 'fixture does not exceed codec bound')
            io.write_certificate_text(target, expected.decode())
            detail = accepted(target, expected)
            require(detail['compressed_parts'] == 0, 'oversized value was compressed')
            return {'value_bytes': len(encode(content['payload'])), **detail}
        test('oversized-writer-legacy-value-fallback', oversized_writer_fallback)

    if args.replay_all:
        def all_replay():
            relative = 'docs/reports/erdos7-odd-covering'
            paths = subprocess.check_output(['git', '-C', str(args.repository), 'ls-files', '-z', '--', relative]).split(b'\0')
            count = compressed = logical_bytes = 0
            accumulated = hashlib.sha256()
            for raw_path in sorted(paths):
                if not raw_path or not raw_path.endswith(b'.json') or b'.parts/' in raw_path: continue
                path = args.repository / raw_path.decode()
                document = parse(path.read_bytes())
                if not isinstance(document, dict) or 'certificate_format' not in document: continue
                standalone, nodes = independent_read(path)
                expected, length = digest(standalone), len(standalone)
                del standalone
                candidate = io.read_artifact_bytes(path)
                require(digest(candidate) == expected and len(candidate) == length, 'replay disagreement: ' + str(path))
                del candidate
                accumulated.update(raw_path + b'\0' + expected.encode() + b'\n')
                count += 1; compressed += nodes; logical_bytes += length
            return {'certificates': count, 'compressed_parts': compressed, 'logical_bytes': logical_bytes,
                    'ordered_path_logical_hash_sha256': accumulated.hexdigest()}
        test('complete-repository-replay', all_replay)
    if args.originals:
        def compare_originals():
            original_paths = sorted(p for p in args.originals.rglob('*') if p.is_file())
            current_base = args.repository / 'docs/reports/erdos7-odd-covering'
            mapping, owners = {}, {}
            for old_path in original_paths:
                relative = old_path.relative_to(args.originals)
                old_hash = digest(old_path.read_bytes())
                current_path = current_base / relative
                new_hash = digest(io.read_artifact_bytes(current_path))
                if old_hash in mapping:
                    require(mapping[old_hash] == new_hash, 'one original hash has divergent current values')
                mapping[old_hash] = new_hash
                owners.setdefault(old_hash, []).append(str(relative))
            token = re.compile(rb'(?<![0-9a-f])[0-9a-f]{64}(?![0-9a-f])')
            replacements = 0
            changed_json = []
            checked_json = 0
            ordered = hashlib.sha256()
            for old_path in original_paths:
                relative = old_path.relative_to(args.originals)
                if relative.suffix != '.json':
                    continue
                original = old_path.read_bytes()
                observed = []
                def substitute(match):
                    key = match[0].decode()
                    result = mapping.get(key, key).encode()
                    if result != match[0]:
                        observed.append({'old': key, 'new': result.decode(), 'owners': owners[key]})
                    return result
                expected = token.sub(substitute, original)
                del original
                actual = io.read_artifact_bytes(current_base / relative)
                require(expected == actual, 'non-pin logical bytes changed: ' + str(relative))
                checked_json += 1
                replacements += len(observed)
                if observed:
                    changed_json.append({'path': str(relative), 'replacements': len(observed)})
                ordered.update(str(relative).encode() + b'\0' + digest(actual).encode() + b'\n')
            require(checked_json > 0, 'no original JSON compared')
            return {'original_artifacts_hashed': len(original_paths), 'json_checked': checked_json,
                    'changed_json': len(changed_json), 'known_source_hash_replacements': replacements,
                    'ordered_path_logical_hash_sha256': ordered.hexdigest()}
        test('original-logical-json-only-known-source-pins-changed', compare_originals)
    passed = sum(row['status'] == 'passed' for row in results)
    print(json.dumps({'summary': {'passed': passed, 'failed': len(results) - passed, 'codec_source_sha256': digest(source.read_bytes())}}))
    return int(passed != len(results))


if __name__ == '__main__':
    raise SystemExit(main())
