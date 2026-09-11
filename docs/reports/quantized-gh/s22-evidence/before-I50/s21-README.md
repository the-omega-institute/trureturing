# S21 composed predecessor evidence

The active [source](../../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md) is the exact 364059-byte S20 predecessor followed by the completed 30675-byte S21 tail. `source-composed-I48` names all 394734 bytes, SHA256 `b462e745a0ef7241a41d138c9bd7169105202bc41ec4cfa38e5674c3cac2023c`. The [composition catalog](composition.json) binds every supported version and alias to its full original identity. Ordinary `file` means the entire file; `file_span` means only its explicit checked interval.

The six raw resources are immutable: [original I37 source](source-I37-original.json), [entire original report](report-I37-original.json), [I32](I32-original.json), [I35](I35-original.json), [I37](I37-original.json), and [completed tail](tail-S21-I37.json). Their 43 ordered parts preserve every original UTF-8 byte, trailing space and LF. Concatenate all parts without separators before parsing. Each part is at most 750 canonical LF lines; every changed evidence file is at most 800 lines and every new directory has at most 40 direct files.

## Version ownership

| Original map | original_source | current_source | original_report | current_report |
| --- | --- | --- | --- | --- |
| I32 | source-pre-I32 | source-I32-current | report-pre-I32 | report-I32-current |
| I35 | source-I32-current | source-I35-current | report-I32-current | report-I35-current |
| I37 | source-I35-current | source-I37-original | report-I35-current | report-I37-original |

`source-I37-original` is the complete original I37 **output**, 347400 bytes. `source-I37-current` is its alias because I37's original `current_source` owns that identity; it never means today's composed source. `source-I37-intake` separately names I37's 347263-byte input. The analogous I32/I35 input aliases and report aliases are explicitly enumerated in the catalog. Historical offsets never implicitly address the growing whole file.

`source-S20-merged`, `source-S20-prefix`, and `source-composed-I47` select exactly source bytes `[0,364059)`, SHA256 `47880f8a0b5b96b7fa2178c5a92284da6ec8b112b33c6e14236719f6963c3d00`. The inherited [S20 API](../s20-evidence/README.md) binds `source-composed-I47` using its existing `file_span` support. All of its original named versions and the complete [S19 contract](../s19-evidence/README.md) retain their meanings.

I37 `/recovery_partitions/I37_intake_source/segments` recovers `source-I35-current` from original I37 source/report slices. I35 `/recovery_partitions/I35_intake_source/segments` then recovers `source-I32-current`. I32 `/recovery_segments` recovers `source-pre-I32` from that I32 source and its own report. I35 `/recovery_partitions/pre_I32_source/segments` is a second exact route, evaluated on I35's original output versions. I37's references to those I35 partitions retain the original document owner. The three earlier reports are exact prefixes of `report-I37-original`, of lengths 91617, 106036 and 137092. No historical program runs during these recoveries.

The original map schemas remain available through `at('I32')`, `at('I35')`, `at('I37')`, their original filenames and repository-relative paths. `at(name, json_pointer)` uses RFC 6901 on the complete raw map. `resolve(ref)` handles I37's actual `document` + `json_pointer` schema and checks the corresponding `immutable_documents` identity. I32 `historical_binding_ref`, `canonical_binding_ref` and current `pair_ref` resolve by atom ID within `original_canonical_bindings`, `current_canonical_bindings` and `new_canonical_pairs`, respectively; reserved unit references resolve within `original_units`. I35 parent/part references resolve only in its `canonical_catalog`; the absent old 32.24 parent stays absent. New I37 pair references resolve only in `new_canonical_pairs`. Stored row pointers address the JSON bytes in I35's `report_evidence_spans/verifier_result`, not a newly executed result.

For byte records, `span(version, record)` requires an explicit version and verifies all supplied identities. In I32, original unit/binding/tail spans belong to `source-pre-I32`; current unit/binding/tail spans belong to `source-I32-current`; destination spans use the explicit source/report path and I32 output owner. Metadata additions likewise use their destination path. In I35, `original_pending_passage.origin_span` belongs to `source-I32-current`; additions/current bindings/parts/uncovered spans belong to `source-I35-current`; report evidence and ingest spans belong to `report-I35-current`. In I37, `original_unit.source_span`, old table/proof and original row coordinates belong to `source-I35-current`; its archive span belongs to `report-I37-original`; new array/proof, current row coordinates and owned units belong to `source-I37-original`. Recovery origin and destination intervals always retain the versions in the table. Shared prefixes retain their named owners even when the bytes agree.

The older report's existing consumers also have exact named inputs. `source-S21-C69` aliases `source-pre-I32`; undoing only its recorded `quantized-gh/` insertion recovers `source-S21-C48`. Removing the ten explicit C48 table-fence literals recovers `source-S21-I16`, including its original failed coverage. `report-S21-C69` aliases `report-pre-I32`; `report-S21-C69-input` is the 78315-byte pre-note prefix, whose single recorded `../` inverse yields `report-S21-C48`. That report's `[10289,78265)` interval yields the entire original `report-S21-I16`. The catalog checks every original identity. Report tables labelled I16, C48 and C69 use these source versions, respectively; their old offsets do not describe the active composition.

## Current units and logical navigation

[current-units.json](current-units.json) retains all 304 original records: 282 S20 predecessor units and 22 S21 units. Its current spans address `source-composed-I48`; inherited `source_version=source-composed-I47` selects the same unchanged prefix through that named version. Its inherited map references use the original S20/S19 APIs (`I29` and `finite-distance-dual-adoption-s19-0911.json` are explicitly exposed here). `own-addresses.json` binds current spans to the composition, historical S21 spans to the original I37 source, and reserved 32.19/32.20 records to original I32. Only preserved tail intervals shift by 47334 bytes. The two original structural headings `[337429,337498)` and `[364059,364127)` remain separate from whole units. Every 32.24 row and its entire proof remain exact.

[canonical-pairs.json](canonical-pairs.json) retains the complete inherited S20 closure and all 78 tail pair records. The 149 imported historical/current pairs, raw producer LF and previous coverage failures remain historical. This API reads no canonical bodies and performs no ingestion.

The four original paths now provide bounded logical entries: [entire report](../actual-5040-fixed-box-0910.md), [I32 map](../theory-body-migration-s21-0910.json), [I35 map](../support-proof-adoption-s21-0910.json), and [I37 map](../support-table-representation-s21-0911.json). The JSON entries declare `s21-logical-entry-v1`; reconstruct the named raw resource to obtain the original schema. The report page restores every original rendered heading anchor and explicit anchor with full-section byte spans and all intersecting raw-part links. `section(anchor)` retrieves the complete section from the original report. Interpret archived source links in their original source context and report links in their original report context, never relative to a raw `.txt` part. Historical absolute paths, commands, `log_ref` and diagnostics are inert attribution and are not followed.

## Preserved corrections and limits

[consumer-repair.json](consumer-repair.json) retains exact pre-I49 metadata/README/navigation archives and the three corrected Git origin paths. The existing [pre-S21 S20 README](s20-readme-before-s21.md) remains byte-exact. I48's README-only extension left S20's real consumer failing with `ValueError('identity mismatch: bytes')`; both declared S21 aliases raised `KeyError`. Those errors and the first I48 structural-coverage failure remain preserved, not relabelled as successes. The I48 report that pinned skill/spec files were unavailable remains an original omission; its cause is unknown and I48 is not claimed to have read them.

This is a representation repair. No source, proof, canonical object, raw historical resource or historical error is rewritten. Fresh complete independent review of the current source and evidence remains caller-owned, as do sealing, commit/push/PR, ordinary CI and ordered delivery. The original source/mathematical scopes and open obligations remain unchanged.

## Fixed reconstruction API

Copy the complete Python APIs from the current S19 and S20 READMEs into `s19_evidence.py` and `s20_evidence.py` in external scratch, then copy the block below into `s21_evidence.py` beside them. Use Python's `-B` option. Set `s21_evidence.ROOT` to the checkout root before consumption, or run from that root. The standard-library recipe reconstructs fixed bytes and JSON only; it never executes archived code, follows opaque references or opens canonical files. `verify()` checks all S21 versions/aliases, map document identities, the complete current unit/structural partition and all report sections. Use returned bytes for external standalone historical copies; JSON reserialization is not a substitute for original map bytes.

```python
"""Fixed S21 reconstruction. Archived code and opaque references stay inert."""
from pathlib import Path
import hashlib
from s19_evidence import Evidence, strict_json, pointer
from s20_evidence import S20Evidence, identity, checked, interval

ROOT = Path('.')
BASE = 'docs/reports/quantized-gh/s21-evidence/'

def file(path):
    p = Path(path)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError('repository-relative physical path required')
    return (ROOT / p).read_bytes()

def read_json(path):
    return strict_json(file(path))

def catalog():
    return read_json(BASE + 'composition.json')

def check(data, expected):
    checked(data, expected)
    extra = {'git_blob_oid': hashlib.sha1(
        b'blob ' + str(len(data)).encode('ascii') + b'\0' + data).hexdigest(),
        'eof_hex': data[-16:].hex()}
    for key in extra.keys() & expected.keys():
        if extra[key] != expected[key]:
            raise ValueError('identity mismatch: ' + key)
    return data

def prefix(data, byte_span):
    return interval(data, byte_span)

def read_parts(name):
    entry = catalog()['versions'][name]
    d = read_json(entry['descriptor'])
    if d['schema'] != 's21-evidence-entry-v1' or d['resource'] != name:
        raise ValueError('wrong resource descriptor')
    if d['original'] != entry['identity']:
        raise ValueError('descriptor/catalog identity differs')
    chunks, cursor, line = [], 0, 1
    for ordinal, part in enumerate(d['parts'], 1):
        b = check(file(part['path']), part)
        if not b or part['ordinal'] != ordinal or part['lines'] > 800:
            raise ValueError('empty, unordered or oversized part')
        if part['byte_span'] != [cursor, cursor + len(b)]:
            raise ValueError('part byte coverage differs')
        if part['line_span'] != [line, line + part['lines'] - 1]:
            raise ValueError('part line coverage differs')
        if ordinal < len(d['parts']) and not b.endswith(b'\n'):
            raise ValueError('interior part must end on LF')
        chunks.append(b)
        cursor += len(b)
        line += part['lf']
    return check(b''.join(chunks), d['original'])

def at(name, json_pointer=''):
    return pointer(strict_json(resource(name)), json_pointer)

def resolve(reference, owner='I37'):
    # The original I37 schema binds document names through immutable_documents.
    binding = at(owner, '/immutable_documents/' + reference['document'])
    data = check(resource(binding['path']), binding)
    return pointer(strict_json(data), reference['json_pointer'])

def span(version, record):
    return check(prefix(resource(version),
                        [record['start_byte'], record['end_byte_exclusive']]), record)

def recover(owner, json_pointer):
    # These are the actual I32 and I35/I37 partition schemas, with explicit owners.
    rows = at(owner, json_pointer)
    versions = catalog()['map_versions'][owner]
    paths = {at(owner, '/source_path'): versions['current_source'],
             at(owner, '/report_path'): versions['current_report']}
    chunks, cursor = [], 0
    for row in rows:
        if owner == 'I32':
            original = row['original_span']
            start, end = original['start_byte'], original['end_byte_exclusive']
        else:
            original = row['identity']
            start, end = row['origin_start_byte'], row['origin_end_byte_exclusive']
        b = check(prefix(resource(paths[row['destination_path']]),
                         [row['destination_start_byte'],
                          row['destination_end_byte_exclusive']]), original)
        if [start, end] != [cursor, cursor + len(b)]:
            raise ValueError('original partition gap, overlap or order differs')
        chunks.append(b)
        cursor = end
    return b''.join(chunks)

def resource(name):
    c = catalog()
    name = c['aliases'].get(name, name)
    if name in c['inherited_resources']:
        return S20Evidence(ROOT, Evidence(ROOT)).raw(c['inherited_resources'][name])
    entry = c['versions'][name]
    kind = entry['kind']
    if kind == 'parts':
        data = read_parts(name)
    elif kind == 'file':
        data = file(entry['path'])
    elif kind == 'file_span':
        data = prefix(file(entry['path']), entry['byte_span'])
    elif kind == 'slices':
        data = b''.join(prefix(resource(s['version']), s['byte_span'])
                        for s in entry['slices'])
    elif kind == 'recovery':
        data = recover(entry['map'], entry['json_pointer'])
    elif kind == 'remove':
        original = resource(entry['version'])
        chunks, cursor = [], 0
        for removal in entry['removals']:
            start, end = removal['byte_span']
            if start < cursor or prefix(original, [start, end]) != removal['literal'].encode('utf-8'):
                raise ValueError('historical inverse literal or order differs')
            chunks.append(original[cursor:start])
            cursor = end
        data = b''.join(chunks) + original[cursor:]
    else:
        raise ValueError('unknown S21 representation kind')
    return check(data, entry['identity'])

def section(anchor):
    nav = read_json(BASE + 'navigation.json')
    row = next(s for s in nav['report_sections']
               if anchor == s['anchor'] or anchor in s['aliases'])
    return check(prefix(resource(nav['report_version']), row['byte_span']), row['identity'])

def verify():
    c = catalog()
    for name in c['versions']:
        resource(name)
    for alias, name in c['aliases'].items():
        if resource(alias) != resource(name):
            raise ValueError('alias differs')
    source = resource('source-composed-I48')
    if source != resource('source-S20-merged') + resource('tail-S21-I37'):
        raise ValueError('source composition differs')
    for owner, versions in c['map_versions'].items():
        for field, version in versions.items():
            check(resource(version), at(owner, '/' + field))
    units = read_json(c['current_units'])['units']
    regions = [(u['span']['byte_start'], u['span']['byte_end_exclusive'], u['span'])
               for u in units]
    regions += [(r['byte_span'][0], r['byte_span'][1], r['identity'])
                for r in c['structural_regions']]
    cursor = 0
    for start, end, expected in sorted(regions):
        if start != cursor:
            raise ValueError('whole-unit/structural coverage differs')
        check(prefix(source, [start, end]), expected)
        cursor = end
    if cursor != len(source):
        raise ValueError('source suffix uncovered')
    for row in read_json(c['navigation'])['report_sections']:
        section(row['anchor'])
    return dict(versions=len(c['versions']), aliases=len(c['aliases']),
                whole_units=len(units), structural_regions=len(c['structural_regions']),
                source=identity(source))
```
