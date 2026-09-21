"""Canonical source binding and semantic certificate IO for Chapter 58."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable canonical module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Context:
    """Keep exact logical source bytes, including a certificate's dependencies."""
    def __init__(self, base, sources, producer):
        self.base = Path(base)
        self.producer = Path(producer)
        self.io = load_module('adaptive_phase_certificate_io', self.base/'certificate_io.py')
        self.source_bytes = {}
        self.visited = set()
        for name in sources:
            self.raw(name)

    def raw(self, name):
        require(not Path(name).is_absolute(), 'report-relative source address')
        raw = self.io.read_artifact_bytes(self.base/name)
        if name in self.source_bytes:
            require(raw == self.source_bytes[name], 'immutable source: ' + name)
        self.source_bytes[name] = raw
        return raw

    def read(self, name):
        return json.loads(self.raw(name), object_pairs_hook=self.io._unique)

    def _dependencies(self, name):
        record = self.read(name)
        if name in self.visited:
            return record
        self.visited.add(name)
        for dependency, digest in record.get('source_sha256', {}).items():
            raw = self.raw(dependency)
            require(sha256(raw).hexdigest() == digest, 'fresh source binding: ' + dependency)
            if dependency.endswith('.json'):
                child = json.loads(raw, object_pairs_hook=self.io._unique)
                if isinstance(child, dict) and isinstance(child.get('source_sha256'), dict):
                    self._dependencies(dependency)
        return record

    def fresh(self, name, producer):
        record = self._dependencies(name)
        digest = record.get('producer_sha256', record.get('verifier_sha256'))
        require(digest == sha256(self.raw(producer)).hexdigest(), 'fresh producer: ' + producer)
        return record

    def finish(self, result):
        require(all(self.io.read_artifact_bytes(self.base/name) == raw
                    for name, raw in self.source_bytes.items()), 'all canonical sources unchanged')
        result['source_sha256'] = {name: sha256(raw).hexdigest()
                                   for name, raw in self.source_bytes.items()}
        result['producer_sha256'] = sha256(self.producer.read_bytes()).hexdigest()
        return result


def run(certificate, calculate, producer):
    parser = argparse.ArgumentParser()
    parser.add_argument('--base', type=Path, default=Path(producer).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = load_module('adaptive_phase_output_io', args.base/'certificate_io.py')
    result = calculate(args.base)
    if args.write:
        io.write_certificate_text(args.base/certificate, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/certificate),
                                     object_pairs_hook=io._unique), 'exact canonical replay')
    print(json.dumps({'schema': result['schema'], 'mode': 'write' if args.write else 'check'}))
