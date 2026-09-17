"""Read and write the report's exact JSON certificates in semantic parts.

Source hashes continue to bind the complete logical JSON bytes. Each physical
part is independently SHA-256 bound; assembly rejects missing, duplicate,
out-of-order, escaped, or unreferenced parts. This is experiment IO, not proof.
"""
from hashlib import sha256
import json
from pathlib import Path
import os
from tempfile import TemporaryDirectory
from urllib.parse import quote

FORMAT = 'erdos7-semantic-certificate-v1'
PART_LINES = 800


def _unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def _bytes(value):
    return (json.dumps(value, indent=2) + '\n').encode('utf-8')


def _keys(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise ValueError('invalid certificate node fields')


def read_artifact_bytes(path):
    """Return raw code/plain JSON bytes, or verified full logical JSON bytes."""
    path = Path(path)
    raw = path.read_bytes()
    if path.suffix != '.json':
        return raw
    document = json.loads(raw, object_pairs_hook=_unique)
    if not isinstance(document, dict) or 'certificate_format' not in document:
        if path.with_name(path.stem + '.parts').exists():
            raise ValueError('parts directory without certificate manifest')
        return raw
    _keys(document, ('certificate_format', 'logical_sha256', 'parts_directory', 'root'))
    if document['certificate_format'] != FORMAT:
        raise ValueError('unknown certificate format')
    expected_directory = path.stem + '.parts'
    if document['parts_directory'] != expected_directory:
        raise ValueError('incorrect parts directory')
    directory = path.parent / expected_directory
    if directory.is_symlink():
        raise ValueError('symlink certificate parts directory')
    seen = set()

    def load(reference):
        if isinstance(reference, dict) and reference.get('kind') == 'inline':
            _keys(reference, ('kind', 'value'))
            return reference['value']
        _keys(reference, ('path', 'sha256', 'kind'))
        name = reference['path']
        relative = Path(name)
        if (not isinstance(name, str) or relative.is_absolute()
                or '..' in relative.parts or relative.as_posix() != name
                or relative.suffix != '.json'):
            raise ValueError('invalid certificate part path')
        part = directory / relative
        ancestry = [directory.joinpath(*relative.parts[:i]) for i in range(1, len(relative.parts) + 1)]
        if not part.resolve().is_relative_to(directory.resolve()) or any(p.is_symlink() for p in ancestry):
            raise ValueError('escaped certificate part')
        if name in seen:
            raise ValueError('duplicate certificate part reference: ' + name)
        seen.add(name)
        payload = part.read_bytes()
        if sha256(payload).hexdigest() != reference['sha256']:
            raise ValueError('certificate part SHA-256 mismatch: ' + name)
        value = json.loads(payload, object_pairs_hook=_unique)
        if reference['kind'] == 'value':
            return value
        if reference['kind'] == 'object':
            if not isinstance(value, dict):
                raise ValueError('object part is not an object')
            return {key: load(child) for key, child in value.items()}
        if reference['kind'] == 'singleton':
            _keys(value, ('item',))
            return [load(value['item'])]
        if reference['kind'] != 'array':
            raise ValueError('invalid certificate part kind')
        _keys(value, ('length', 'chunks'))
        if type(value['length']) is not int or value['length'] < 0:
            raise ValueError('invalid certificate array length')
        if not isinstance(value['chunks'], list):
            raise ValueError('invalid certificate array chunks')
        result = []
        for chunk in value['chunks']:
            _keys(chunk, ('start', 'stop', 'part'))
            start, stop = chunk['start'], chunk['stop']
            if type(start) is not int or type(stop) is not int or start != len(result) or stop <= start:
                raise ValueError('non-contiguous certificate interval')
            rows = load(chunk['part'])
            if not isinstance(rows, list) or len(rows) != stop - start:
                raise ValueError('certificate interval length mismatch')
            result.extend(rows)
        if len(result) != value['length']:
            raise ValueError('incomplete certificate array')
        return result

    value = load(document['root'])
    actual = {p.relative_to(directory).as_posix() for p in directory.rglob('*') if p.is_file()}
    if actual != seen:
        raise ValueError('unreferenced or missing certificate parts')
    logical = _bytes(value)
    if sha256(logical).hexdigest() != document['logical_sha256']:
        raise ValueError('complete logical certificate SHA-256 mismatch')
    return logical


def read_artifact_text(path, encoding='utf-8', errors=None):
    return read_artifact_bytes(path).decode(encoding, errors or 'strict')


def _write_semantic_certificate(path, text):
    """Build a new partition only inside the caller's empty staging directory."""
    directory = path.with_name(path.stem + '.parts')
    value = json.loads(text, object_pairs_hook=_unique)
    logical = _bytes(value)
    if logical.decode('utf-8') != text:
        raise ValueError('long certificate must use canonical indent=2 JSON')
    directory.mkdir(parents=True)

    def save(value, route):
        encoded = _bytes(value)
        kind = 'value'
        if len(encoded.splitlines()) > PART_LINES and isinstance(value, dict):
            kind = 'object'
            original = value
            value = {key: ({'kind': 'inline', 'value': child}
                           if len(_bytes(child).splitlines()) <= 40
                           else save(child, route + f'/{index:03d}-' + quote(key, safe='')))
                     for index, (key, child) in enumerate(original.items())}
            for index, (key, child) in enumerate(original.items()):
                if len(_bytes(value).splitlines()) <= PART_LINES:
                    break
                if value[key]['kind'] == 'inline' and len(_bytes(child).splitlines()) > 5:
                    value[key] = save(child, route + f'/{index:03d}-' + quote(key, safe=''))
            encoded = _bytes(value)
        elif len(encoded.splitlines()) > PART_LINES and isinstance(value, list):
            kind = 'array'
            chunks, start = [], 0
            while start < len(value):
                stop = start + 1
                while stop < len(value) and len(_bytes(value[start:stop+1]).splitlines()) <= PART_LINES:
                    stop += 1
                child = value[start:stop]
                if len(child) == 1 and len(_bytes(child).splitlines()) > PART_LINES:
                    # Preserve the single array element while splitting its fields.
                    item = save(child[0], route + f'/{start:06d}/item')
                    part = store({'item': item}, route + f'/{start:06d}/single', 'singleton')
                else:
                    part = save(child, route + f'/{start:06d}-{stop:06d}')
                chunks.append({'start': start, 'stop': stop, 'part': part})
                start = stop
            encoded = _bytes({'length': len(value), 'chunks': chunks})
        return store_bytes(encoded, route, kind)

    def store(value, route, kind):
        return store_bytes(_bytes(value), route, kind)

    def store_bytes(encoded, route, kind):
        if len(encoded.splitlines()) > 1000:
            raise ValueError('certificate descriptor exceeds file capacity')
        name = route + '.json'
        target = directory / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(encoded)
        return {'path': name, 'sha256': sha256(encoded).hexdigest(), 'kind': kind}

    root = save(value, 'content')
    manifest = {'certificate_format': FORMAT, 'logical_sha256': sha256(logical).hexdigest(),
                'parts_directory': directory.name, 'root': root}
    path.write_bytes(_bytes(manifest))
    if read_artifact_bytes(path) != logical:
        raise ValueError('written certificate failed exact reassembly')
    return len(text)


def write_certificate_text(path, text, encoding='utf-8', errors=None):
    """Stage, verify, and publish a complete certificate with exception rollback."""
    path = Path(path)
    if path.suffix != '.json':
        return path.write_text(text, encoding=encoding, errors=errors)
    directory = path.with_name(path.stem + '.parts')
    if directory.exists() or directory.is_symlink():
        # Validate ownership, all parts, and the old logical bytes before touching it.
        read_artifact_bytes(path)
    with TemporaryDirectory(prefix='.' + path.stem + '-write-', dir=path.parent) as temporary:
        staging = Path(temporary)
        candidate = staging / path.name
        if len(text.splitlines()) > 1000:
            _write_semantic_certificate(candidate, text)
        else:
            json.loads(text, object_pairs_hook=_unique)
            candidate.write_text(text, encoding=encoding, errors=errors)
        expected = text.encode(encoding, errors or 'strict')
        if read_artifact_bytes(candidate) != expected:
            raise ValueError('staged certificate failed exact reassembly')
        candidate_parts = candidate.with_name(candidate.stem + '.parts')
        previous_parts = staging / 'previous.parts'
        saved_old_parts = False
        installed_new_parts = False
        try:
            if directory.exists():
                os.replace(directory, previous_parts)
                saved_old_parts = True
            if candidate_parts.exists():
                os.replace(candidate_parts, directory)
                installed_new_parts = True
            # Commit last: until this succeeds the original manifest is untouched.
            os.replace(candidate, path)
        except BaseException:
            if installed_new_parts:
                os.replace(directory, candidate_parts)
            if saved_old_parts:
                os.replace(previous_parts, directory)
            raise
    return len(text)
