# S19 fixed evidence representation

The [report navigation page](../balanced-prime-235-all-slabs-0910.md) and the four map entry points use a new physical representation. The maps declare `s19-evidence-entry-v1`; they are descriptors, not instances of the old map schemas. The only current consumption contract is this API with [catalog.json](catalog.json). Calling `Evidence.json("I36")` returns the complete original I36 JSON object. Calling `Evidence.provenance()` returns the explicit current C97 evidence-gap resolution. These are distinct operations; neither silently rewrites history.

## Resource identity and interpretation

A logical original resource is its name **and full SHA256**, with the byte length, LF count and terminal LF count in its descriptor. The catalog binds each name to that exact identity. `I31`, `I33`, `I36` and `I42` name the original maps at commit `3a7f81337a673c09df19ed69d3bf5024eeef2600`; `report` names the original 224423-byte report at that commit. Repository-relative and bare map filenames are aliases for those versions, never for descriptor JSON. There is no unversioned current-source alias.

Each descriptor has `schema`, `resource`, `logical_path`, `original`, `origin`, `contract`, `interpretation` and `parts`. Only the I36 descriptor additionally owns `current_provenance`. `original` records bytes, SHA256, actual LF bytes, integer trailing LF bytes and canonical lines. Each part records its ordinal, repository-relative path, zero-based half-open byte interval, one-based inclusive LF line interval, those same identity fields, and a contextual label. Labels are navigation metadata, not replacement evidence. Index arrays use one complete readable record per LF. Original JSON was never serialized again.

Parts under `raw/<resource>-<original-hash-prefix>/group-NNN/part-NNNN-<part-hash-prefix>.txt` contain only exact ordered contiguous original byte slices. Paths include a deterministic original-resource identity, part ordinal and part identity; the full digests are in the descriptor. Each part is strict UTF-8 and at most 800 canonical LF lines. Groups contain at most 40 direct files, below the requested 47 and repository admission limit 48. Splits prefer nearby JSON object/list or Markdown section/paragraph boundaries. The final part preserves all original trailing LF, including absence of a terminator. No header, delimiter, BOM, compression, escaping or LF trimming is added to raw parts. A JSON part can be a fragment: concatenate every part before parsing the original JSON. The `.txt` extension declares archival text, not a competing live schema or a binary/excluded storage path.

## Public material

All entries below are stored in this checkout. Their original source paths, task IDs and opaque references remain unchanged in the raw resources. A local diagnostic path or `log_ref` occurring in historical text is attribution only; this recipe never follows it. The complete report, its embedded fixed certificate text and all its source archives are recoverable without those references, the dispatch ZIP, a caller temporary directory or a historical program.

| Resource | Complete part index | Direct readable parts |
| --- | --- | --- |
| report | [report](indexes/report.json) | [0001](raw/report-380990dd23fe/group-001/part-0001-953c81343cd2.txt), [0002](raw/report-380990dd23fe/group-001/part-0002-0b62815d7f9a.txt), [0003](raw/report-380990dd23fe/group-001/part-0003-a25c206d72b7.txt), [0004](raw/report-380990dd23fe/group-001/part-0004-6c0d748f2c82.txt), [0005](raw/report-380990dd23fe/group-001/part-0005-21e5f609b22b.txt) |
| I31 | [I31](../theory-body-migration-s19-0910.json) | [All 248 parts](indexes/i31-parts.md) |
| I33 | [I33](../theory-proof-adoption-s19-0910.json) | [All 89 parts](indexes/i33-parts.md) |
| I36 | [I36](../finite-distance-dual-adoption-s19-0911.json) | [0001](raw/i36-9be8bd12f2b1/group-001/part-0001-cd57fc7f554c.txt), [0002](raw/i36-9be8bd12f2b1/group-001/part-0002-ce3b34e57174.txt), [0003](raw/i36-9be8bd12f2b1/group-001/part-0003-a01d375c5b67.txt), [0004](raw/i36-9be8bd12f2b1/group-001/part-0004-1098c7548fa3.txt), [0005](raw/i36-9be8bd12f2b1/group-001/part-0005-14a0f31786a8.txt), [0006](raw/i36-9be8bd12f2b1/group-001/part-0006-2dfbbacb204b.txt), [0007](raw/i36-9be8bd12f2b1/group-001/part-0007-d4d8f7cb3d80.txt), [0008](raw/i36-9be8bd12f2b1/group-001/part-0008-b36efd73ae56.txt), [0009](raw/i36-9be8bd12f2b1/group-001/part-0009-97d8bdd64815.txt), [0010](raw/i36-9be8bd12f2b1/group-001/part-0010-72e562095e9c.txt), [0011](raw/i36-9be8bd12f2b1/group-001/part-0011-cd69d0221f72.txt), [0012](raw/i36-9be8bd12f2b1/group-001/part-0012-83db54fba1d7.txt), [0013](raw/i36-9be8bd12f2b1/group-001/part-0013-1238dc0e105f.txt), [0014](raw/i36-9be8bd12f2b1/group-001/part-0014-12ae4dc4dcfb.txt), [0015](raw/i36-9be8bd12f2b1/group-001/part-0015-25c5fb84884c.txt), [0016](raw/i36-9be8bd12f2b1/group-001/part-0016-c1e1f25afe03.txt), [0017](raw/i36-9be8bd12f2b1/group-001/part-0017-7634da45b9d5.txt), [0018](raw/i36-9be8bd12f2b1/group-001/part-0018-725c3d1cc0ff.txt), [0019](raw/i36-9be8bd12f2b1/group-001/part-0019-3f1b4b5a9695.txt) |
| I42 | [I42](../theory-section12-migration-s19-0911.json) | [0001](raw/i42-b3ad997b990a/group-001/part-0001-d55d9836a9eb.txt), [0002](raw/i42-b3ad997b990a/group-001/part-0002-8d1038ad87fd.txt), [0003](raw/i42-b3ad997b990a/group-001/part-0003-28aacc646e03.txt), [0004](raw/i42-b3ad997b990a/group-001/part-0004-cca2f7ad10bc.txt), [0005](raw/i42-b3ad997b990a/group-001/part-0005-47632d658ff8.txt), [0006](raw/i42-b3ad997b990a/group-001/part-0006-a9dc6e4e7497.txt), [0007](raw/i42-b3ad997b990a/group-001/part-0007-0b86fa658982.txt), [0008](raw/i42-b3ad997b990a/group-001/part-0008-b0bd20b2415f.txt), [0009](raw/i42-b3ad997b990a/group-001/part-0009-f95db51acf3e.txt), [0010](raw/i42-b3ad997b990a/group-001/part-0010-3cd1fe07a814.txt), [0011](raw/i42-b3ad997b990a/group-001/part-0011-81d9dad19cc5.txt) |
| C88 | [C88](indexes/c88.json) | [0001](raw/c88-bb219d68ff32/group-001/part-0001-bb219d68ff32.txt) |
| C90 | [C90](indexes/c90.json) | [0001](raw/c90-fbc480245062/group-001/part-0001-fbc480245062.txt) |
| C92 | [C92](indexes/c92.json) | [0001](raw/c92-08aa274e3359/group-001/part-0001-08aa274e3359.txt) |
| C93 | [C93](indexes/c93.json) | [0001](raw/c93-05ff29453e53/group-001/part-0001-05ff29453e53.txt) |
| C95 | [C95](indexes/c95.json) | [0001](raw/c95-256d01e524f3/group-001/part-0001-256d01e524f3.txt) |
| C96 | [C96](indexes/c96.json) | [0001](raw/c96-0bd3cb477f46/group-001/part-0001-0bd3cb477f46.txt) |
| C97 | [C97](indexes/c97.json) | [0001](raw/c97-e06f1200c3fc/group-001/part-0001-e06f1200c3fc.txt) |
| C97-intake | [C97-intake](indexes/c97-intake.json) | [0001](raw/c97-intake-49ba86d66bbb/group-001/part-0001-49ba86d66bbb.txt) |
| CI-intake | [CI-intake](indexes/ci-intake.json) | [0001](raw/ci-intake-9666fb199691/group-001/part-0001-9666fb199691.txt) |
| CI-excerpt | [CI-excerpt](indexes/ci-excerpt.json) | [0001](raw/ci-excerpt-c3c194bdf8ca/group-001/part-0001-c3c194bdf8ca.txt) |

The seven C88/C90/C92/C93/C95/C96/C97 envelopes retain every original raw byte and parsed value. Their reported statuses, errors, corrections and primary-author limitations remain historical. Primary scalar inventories in I36 continue to address those named envelopes. I33's earlier input/index correspondence remains attached to its original inputs. Collection pointers incorporate every nested member. No inventory is replaced by a count.

## Version ownership, spans and recovery

`at(name, pointer)` implements RFC 6901 against the reconstructed original JSON. Empty pointer means the whole object; `~0` and `~1` are decoded in the standard order. `resolve(reference, owner)` uses an explicitly named `map` or primary `input`, otherwise the original owner. Bare `binding` and `identity_binding` pointers stay within their original map. I36 primary leaf pointers are relative to the enclosing C95/C96/C97 input, whereas each leaf's provenance binding is relative to I36. `verify_references()` checks those exact existing cases and scalar digests.

`span(version, record)` requires a named byte-resource version, checks half-open bounds and every supplied raw hash/length/LF field, and returns exact bytes. `owner_span(map, pointer)` uses [105 explicit ownership rules](span-owners.json) covering all 15496 existing span records; the rules bind their original source/report versions. Repeated spans with an unchanged prefix still retain the named owner's version. Numeric, dotted-numeric and 64-hex pointer components are normalized to `*` only for matching these documented original-schema record families. Unknown families fail closed. These rules are the new representation's explicit ownership table, not a runtime guess from whatever current file happens to exist.

| Original map | Its source before change | Its source after change | Its final report |
| --- | --- | --- | --- |
| I31 | source-pre-I31 | source-I31 | report-I31 |
| I33 | source-I31 | source-I33 | report-I33 |
| I36 | source-I33 | source-I36 | report-I36 |
| I42 | source-I36 | source-I42 | report |

The catalog defines all source versions from the fixed source-I42 interval in the growing active file and exact source/report slices. It reconstructs source-I36 by restoring report[222353:224011] between source-I42[0:27206] and source-I42[29358:337429]. Next it consumes I36 `/recovery/original_i36_source` with source-I36, then I33 `/recovery/i33_original_source` with source-I33, then I31 `/recovery_spans` with source-I31. Rows remain in increasing original offset order; every original/current payload identity and contiguous original coverage is checked. The separate I33 `/recovery/pre_i31_original_source` route must produce identical pre-I31 bytes. `source-scientific-base` is the exact historical 254298-byte prefix of that source. Report versions are named exact prefixes, not copies of this navigation page.

I42's full composition, address transform, 262-unit inventory, 354-pair inventory, 38 ordered chains, all inherited dispositions and prior corrections remain available by their original pointers. This representation preserves their values and version-bound references; it does not re-ingest, re-scan the physical canonical corpus or renew their scientific review. The 674 occurrence spans without local hashes are checked against their enclosing original CAS identity records using source bytes only. The remaining hash-free span is I33's report digest hole.

The I33 report contract uses the complete **original I33 map hash**, not the hash of its compact descriptor. `report-I33` equals its 218261-byte payload plus `/report_binding/footer_template_utf8` with that original hash substituted. Its masked hash replaces only report[218374:218438] with 64 ASCII zeros. The full original report and every prefix retain their own unmasked identities. Source recoveries, report partitions, proof text, archived erroneous values and all primary mappings retain the same ownership.

## Navigation and current provenance

The current report page provides every section's original interval, contextual heading and all intersecting raw part links. In particular, the substantive `i31-inactive-archive` entry covers the complete inactive archive required by the frozen source's five proof links. The two other source links to the report still lead to the complete report and its input mappings. `section(anchor)` returns the full original section bytes. Rendering a raw fragment on its own does not change historical relative-link or fence semantics: interpret those in the named original report, and use the current page for navigation. The report's original pre-relocation `../develop/theory/...` link text is retained as history; the current page links the frozen source correctly at `../../develop/theory/...`. Archived source links keep their source-origin context. No historical link string is silently rewritten.

The current I36 descriptor alone records C97 as `kind=failure, state=resolved`: the missing public evidence gap is resolved by completed import `66de8069-0171-4543-9caa-d8a065282093`. Original task `4b113aea-c074-4750-98bd-40363326d9eb` remains failed with `prompt_delivery_uncertain`. The original untyped node is unchanged in `Evidence.at("I36", "/provenance_and_review_limits/primary_recovery/C97")`. The typed current record binds the complete recovered visible envelope (30200 bytes, SHA256 `e06f1200c3fcb38381f64af69e50883d96c99962c88ef6b126acab747543e6aa`) and caller intake (2974 bytes, SHA256 `49ba86d66bbbd9994e26730e4214274efa9235bef33387fd87875dea4b85bdb6`). It attests neither original author serialization nor generation time nor serving identity. It asserts nothing about RH. No Lean TASK case is invented, and SL019 is unchanged.

The prior R5 review applies to its old exact snapshot. This layout needs fresh independent full review and actual CI under caller ownership. Mathematical proofs, canonical membership and producer bytes remain inherited; reconstruction, references, spans, links, capacity and the current provenance binding are the new representation checks. These are not source adoption, new mathematics, a CI-green verdict, independent approval, delivery or whole-goal completion. PR6741 remains closed unmerged and the standing goal remains active.

## Append composition contract (I47)

`source-I42` now uses the explicit catalog `file_span` form: `path`, `byte_start=0`, and `byte_end_exclusive=337429`. The API checks integer bounds against the physical file, selects exactly that interval, then checks the existing full historical identity. It does not infer a prefix length from a digest or silently truncate a `file` input. The `file` form still reads and verifies the entire file. All existing resource aliases, original source/report versions, recovery routes, spans, provenance and I33 footer semantics retain their meanings.

The exact preceding [README](../s20-evidence/s19-readme-before.json) and [catalog](../s20-evidence/s19-catalog-before.json) are retained as bounded raw text with their `56aebf5d4573c953d6a994f019d8abb216d5bf35` provenance. The [S20 contract](../s20-evidence/README.md) reconstructs those bytes. Their old whole-file API was valid for its 337429-byte snapshot and is not claimed to work unchanged after chapter 31 is appended. This small current-consumer extension changes representation only; all historical findings and independent-review limits remain attributed to their original stages.

## Fixed representation recipe

Copy only the following Python block into a file **outside the repository**, for example `/tmp/s19_evidence.py`. It uses only the Python standard library. Run `python3 -B /tmp/s19_evidence.py /path/to/checkout` to verify reconstruction and references. The block never executes code from any archived resource, opens opaque references, accesses the network, or reads CAS/YAML files. The recipe's own JSON/span operations are representation logic.

For individual access, import that file, construct `e = Evidence("/path/to/checkout")`, and use `e.raw("I31")`, `e.json("I36")`, `e.at("I42", "/composition")`, `e.owner_span("I42", "/report/append/payload")`, or `e.section("i31-inactive-archive")`. Write returned bytes with `Path("/outside/checkout/original.json").write_bytes(e.raw("I31"))` for an exact standalone original; never serialize its parsed JSON as a substitute for the original bytes. `e.provenance()` reads the current resolution separately.

```python
"""Fixed S19 evidence representation API. No historical program is executed."""
from pathlib import Path
import hashlib
import json
import re

PREFIX = 'docs/reports/quantized-gh/s19-evidence/'
SOURCE = 'docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('duplicate JSON key: ' + key)
            result[key] = value
        return result
    def invalid(value):
        raise ValueError('non-JSON numeric constant: ' + value)
    return json.loads(data.decode('utf-8', errors='strict'),
                      object_pairs_hook=pairs, parse_constant=invalid)

def pointer(value, path):
    if path == '':
        return value
    if not path.startswith('/'):
        raise ValueError('RFC 6901 pointer must be empty or start with /')
    for token in path[1:].split('/'):
        if re.search(r'~(?![01])', token):
            raise ValueError('invalid JSON pointer escape')
        token = token.replace('~1', '/').replace('~0', '~')
        if isinstance(value, list):
            if not re.fullmatch(r'0|[1-9][0-9]*', token):
                raise ValueError('invalid JSON array index')
            value = value[int(token)]
        else:
            value = value[token]
    return value

def walk(value, path=''):
    yield path, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from walk(child, path+'/'+key.replace('~','~0').replace('/','~1'))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from walk(child, path+'/'+str(index))

def check_identity(data, expected):
    data.decode('utf-8', errors='strict')
    observed = {'sha256': digest(data), 'bytes': len(data),
                'lf': data.count(b'\n'),
                'terminal_lf': len(data)-len(data.rstrip(b'\n')),
                'lines': data.count(b'\n')+(0 if data.endswith(b'\n') else 1)}
    aliases = {'byte_count':'bytes', 'lf_count':'lf',
               'terminal_lf_count':'terminal_lf'}
    for key, value in expected.items():
        field = aliases.get(key, key)
        if field in observed:
            if isinstance(value, bool):
                raise ValueError('boolean is not an integer count: '+key)
            if value != observed[field]:
                raise ValueError('identity mismatch: '+key)
    return data

class Evidence:
    def __init__(self, root):
        self.root = Path(root)
        self.catalog = strict_json(self.read_file(PREFIX+'catalog.json'))
        if self.catalog['schema'] != 's19-evidence-catalog-v1':
            raise ValueError('unknown catalog schema')
        self.cache = {}
        self.documents = {}

    def read_file(self, path):
        p = Path(path)
        if p.is_absolute() or '..' in p.parts:
            raise ValueError('only repository-relative physical paths are read')
        return (self.root/p).read_bytes()

    def name(self, name):
        if name in self.catalog['resources'] or name in self.catalog['versions']:
            return name
        return self.catalog['aliases'][name]

    def entry(self, name):
        name = self.name(name)
        item = self.catalog['resources'][name]
        entry = strict_json(self.read_file(item['entry']))
        if entry['schema'] != 's19-evidence-entry-v1' or entry['resource'] != name:
            raise ValueError('wrong entry identity')
        if entry['original'] != item['original'] or entry['logical_path'] != item['logical_path']:
            raise ValueError('entry/catalog mismatch')
        return entry

    def raw(self, name):
        name = self.name(name)
        if name in self.cache:
            return self.cache[name]
        if name in self.catalog['resources']:
            entry = self.entry(name)
            chunks, cursor, line_cursor = [], 0, 1
            for ordinal, part in enumerate(entry['parts'], 1):
                if part['ordinal'] != ordinal or part['byte_start'] != cursor:
                    raise ValueError('noncontiguous or reordered archive')
                b = check_identity(self.read_file(part['path']), part)
                if not b or part['lines'] > 800:
                    raise ValueError('empty or over-capacity part')
                cursor += len(b)
                if cursor != part['byte_end_exclusive'] or part['line_start'] != line_cursor:
                    raise ValueError('incorrect byte/line coverage')
                if part['line_end_inclusive'] != line_cursor+part['lines']-1:
                    raise ValueError('incorrect line endpoint')
                if ordinal < len(entry['parts']) and not b.endswith(b'\n'):
                    raise ValueError('non-final part does not end on LF')
                line_cursor += b.count(b'\n')
                chunks.append(b)
            data = b''.join(chunks)
            check_identity(data, entry['original'])
        else:
            version = self.catalog['versions'][name]
            if 'file_span' in version:
                binding = version['file_span']
                data = self.read_file(binding['path'])
                start, end = binding['byte_start'], binding['byte_end_exclusive']
                if type(start) is not int or type(end) is not int or not 0 <= start <= end <= len(data):
                    raise ValueError('invalid explicit file span')
                data = data[start:end]
            elif 'file' in version:
                data = self.read_file(version['file'])
            elif 'slices' in version:
                data = b''.join(self.span(s['resource'], s) for s in version['slices'])
            else:
                r = version['recovery']
                data = self.recover(r['map'], r['pointer'], r['source_input'], r['report_input'])
            check_identity(data, version['original'])
        self.cache[name] = data
        return data

    def json(self, name):
        name = self.name(name)
        if name not in self.documents:
            self.documents[name] = strict_json(self.raw(name))
        return self.documents[name]

    def at(self, name, path=''):
        return pointer(self.json(name), path)

    def resolve(self, reference, owner):
        # A bare pointer is relative to its named original owner.
        if isinstance(reference, str):
            return self.at(owner, reference)
        return self.at(reference.get('map', reference.get('input', owner)), reference['pointer'])

    def span(self, version, record):
        # Version is mandatory: never apply an old source/report offset to a page.
        data = self.raw(version)
        start, end = record['byte_start'], record['byte_end_exclusive']
        if type(start) is not int or type(end) is not int or not 0 <= start <= end <= len(data):
            raise ValueError('invalid span')
        return check_identity(data[start:end], record)

    def recover(self, owner, path, source_version, report_version='report'):
        rows = self.at(owner, path)
        cursor, pieces = 0, []
        for row in rows:
            old, new = row['original'], row['current']
            if old['byte_start'] != cursor:
                raise ValueError('original recovery coverage gap/overlap/order')
            version = source_version if new.get('path', SOURCE) == SOURCE else report_version
            piece = self.span(version, new)
            check_identity(piece, old)
            cursor += len(piece)
            if cursor != old['byte_end_exclusive']:
                raise ValueError('incorrect original recovery endpoint')
            pieces.append(piece)
        return b''.join(pieces)

    def provenance(self):
        binding = self.catalog['current_provenance']
        return pointer(strict_json(self.read_file(binding['entry'])), binding['pointer'])

    def section(self, anchor):
        nav = strict_json(self.read_file(PREFIX+'navigation.json'))
        section = next(s for s in nav['sections'] if s['anchor'] == anchor)
        return self.span('report', {'byte_start':section['start'], 'byte_end_exclusive':section['end']})

    def owner_span(self, owner, path):
        node = self.at(owner, path)
        rules = strict_json(self.read_file(PREFIX+'span-owners.json'))['rules']
        pattern = re.sub(r'/(?:\d+(?:\.\d+)*|[0-9a-f]{64})(?=/|$)', '/*', path)
        matches = [r for r in rules if r['owner'] == self.name(owner)
                   and r['pointer_pattern'] == pattern and r['record_path'] == node.get('path')]
        if len(matches) != 1:
            raise ValueError('span requires one explicit version owner')
        return self.span(matches[0]['version'], node)

    def verify_spans(self):
        rules = strict_json(self.read_file(PREFIX+'span-owners.json'))['rules']
        index = {(r['owner'],r['pointer_pattern'],r['record_path']):r for r in rules}
        if len(index) != len(rules):
            raise ValueError('duplicate ownership rule')
        counts = {key:[0,0] for key in index}
        for owner in ['I31','I33','I36','I42']:
            for path, node in walk(self.json(owner)):
                if not isinstance(node, dict) or not {'byte_start','byte_end_exclusive'} <= node.keys():
                    continue
                pattern = re.sub(r'/(?:\d+(?:\.\d+)*|[0-9a-f]{64})(?=/|$)', '/*', path)
                key = (owner,pattern,node.get('path'))
                rule = index[key]
                payload = self.span(rule['version'], node)
                if 'sha256' not in node and ('/original_occurrences/' in path
                                              or '/current_source_occurrences/' in path):
                    parent = self.at(owner, path.rsplit('/',2)[0])
                    check_identity(payload, parent['cas'])
                counts[key][0] += 1
                counts[key][1] += int('sha256' in node)
        for key, (total, hashed) in counts.items():
            if total != index[key]['records'] or hashed != index[key]['hashed_records']:
                raise ValueError('ownership coverage differs')
        return {'span_records':sum(c[0] for c in counts.values()),
                'hashed_span_records':sum(c[1] for c in counts.values()),
                'span_owner_rules':len(rules)}

    def verify_references(self):
        count, scalar_hashes = 0, 0
        for owner in ['I31','I33','I36','I42']:
            for location, node in walk(self.json(owner)):
                if not isinstance(node, dict):
                    continue
                if 'pointer' in node and isinstance(node['pointer'], str):
                    target = node.get('map', node.get('input', owner))
                    if owner == 'I36' and location.startswith('/primary_correspondence/'):
                        index = int(location.split('/')[2])
                        target = self.json(owner)['primary_correspondence'][index]['input']
                    value = self.at(target, node['pointer'])
                    count += 1
                    if 'value_sha256' in node:
                        encoded = json.dumps(value, ensure_ascii=False, sort_keys=True,
                                             separators=(',', ':')).encode('utf-8')
                        if digest(encoded) != node['value_sha256']:
                            raise ValueError('primary scalar hash mismatch: '+location)
                        scalar_hashes += 1
                for key in ['binding', 'identity_binding']:
                    if isinstance(node.get(key), str) and node[key].startswith('/'):
                        self.at(owner, node[key])
                        count += 1
        return {'json_pointer_records':count, 'primary_scalar_hashes':scalar_hashes}

    def verify(self):
        for name in self.catalog['resources']:
            self.raw(name)
            if self.catalog['resources'][name]['logical_path'].endswith('.json'):
                self.json(name)
        for name in self.catalog['versions']:
            self.raw(name)
        alternate = self.recover('I33','/recovery/pre_i31_original_source','source-I33')
        if alternate != self.raw('source-pre-I31'):
            raise ValueError('independent pre-I31 recovery routes disagree')
        binding = self.at('I33','/report_binding')
        report = self.raw('report-I33')
        footer = binding['footer_template_utf8'].replace('{map_sha256}',digest(self.raw('I33'))).encode('utf-8')
        if self.span('report',binding['payload_prefix'])+footer != report:
            raise ValueError('I33 report footer differs')
        hole = binding['map_sha256_hole']
        masked = report[:hole['byte_start']]+b'0'*64+report[hole['byte_end_exclusive']:]
        if digest(masked) != binding['masked_sha256']:
            raise ValueError('I33 report masked hash differs')
        historical = self.at('I36','/provenance_and_review_limits/primary_recovery/C97')
        current = self.provenance()
        intake = self.json('C97-intake')
        if current['kind'] != 'failure' or current['state'] != 'resolved':
            raise ValueError('C97 evidence gap must be explicitly resolved')
        for key, value in historical.items():
            if current[key] != value:
                raise ValueError('C97 history differs')
        if current['original_task_status'] != 'failed' or intake['import_status'] != 'completed':
            raise ValueError('failed task and completed import must remain distinct')
        if intake['source_task_id'] != current['failed_source_task'] or intake['read_only_import_task'] != current['completed_import']:
            raise ValueError('C97 public intake identity differs')
        if digest(self.raw('C97')) != intake['visible_envelope_sha256']:
            raise ValueError('C97 recovered public envelope binding differs')
        return dict(raw_resources=len(self.catalog['resources']),
                    named_versions=len(self.catalog['versions']),
                    **self.verify_references(), **self.verify_spans())

if __name__ == '__main__':
    import sys
    evidence = Evidence(sys.argv[1])
    print(json.dumps(evidence.verify(), sort_keys=True))
```
