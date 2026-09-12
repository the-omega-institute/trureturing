# S24 composed predecessor evidence

The [mathematical volume](../../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md) is the exact440285-byte actual S23 predecessor followed immediately by the complete original32331-byte chapter35 tail, with zero separator bytes. The composed472616 bytes /9390 LF have SHA256 `9b73326f45cd654d6287ace8daf0a2e35c983d5912c67020036281ddb8b6eabe`. Every inherited whole unit and all28 owned units are unchanged.

[composition.json](composition.json) binds complete named versions; [current-units.json](current-units.json) and [source-boundaries.json](source-boundaries.json) partition all373 whole units and five structural headings. [own-addresses.json](own-addresses.json) keeps35.28 and35.30 permanently external. The original header is `[440285,440369)`;35.29 is `[471474,472616)`, with ordered1006-byte and136-byte children. The real receipt field is `chain_atoms`; an empty `children` array cannot establish a leaf.

## Complete original resources

| Resource | Complete logical object |
|---|---|
| source-composed-I54 | Entire current physical source; ordinary `file` |
| source-S23-merged | Exact original source through explicit `[0,440285)` |
| tail-S24-I28 | Complete original chapter35, `[440285,472616)` |
| source-I28-original / source-I28-current |426629-byte original I28 source: complete original I20 source, historical extra LF, complete tail |
| source-pre-I28-original / source-I28-intake |432403-byte original pre-I28 source through all77 original source/archive intervals |
| report-I28-original / report-I28-current |114566-byte original report, including every raw response, error and EOF variant |
| report-pre-I28-original / report-I28-intake |88644-byte original report prefix |
| I28-original / I28 |250090-byte original typed map, exact JSON bytes and distinct schema |
| upstream-residual-before-cover | Exact328-byte historical residual row, archived as raw evidence |
| upstream-closed-current | Actual489-byte inherited absorbed-closed row; no new formalization |

Every parts descriptor under [entries](entries/) gives complete identities and disjoint byte/line intervals. Concatenate the transparent raw parts in order before parsing. Parts are at most750 actual LF lines; subordinate evidence is at most800 lines and new directories at most40 direct files. No compressed or encoded logical body is used. The full mathematical volume is separate.

[Source inverse](source-inverse.json) retains all77 original intervals. The original394297-byte mixed prefix and its extra LF through394298 remain historical; that LF belongs to original34.22. It does not replace current pure34.22. Original raw report/source links retain their logical owner, regardless of physical part placement. The original map pathname resolves to the full I28 map through this API, while its physical file is a bounded entry.

## Current and historical canonical data

[Imports](imports.json) records exactly122 absent original Git objects, copied byte-for-byte with their original modes. No ingest ran. The [current catalog](canonical-catalog.json) contains586 retained pairs;373 current roots reach502 pairs, with84 historical-only pairs and54 ordered chains. These are representation counts, not new kernel or mathematical results.

The current catalog overlays the one upstream covered-row move identified in [upstream-covered-row.json](upstream-covered-row.json). `canonical_record(atom, 'current')` names the actual closed row and its existing coverage edge. `canonical_record(atom, 'S23-original')` names the exact archived residual bytes through an explicit historical resource. The former residual pathname is never recreated or silently aliased by `file()`. Historical S19–S23 catalogs retain their own original coordinates; use this version-aware canonical consumer to recover old row bytes. The separate excluded40e660de alias remains absent.

For fixed-cache audits, `canonical_bytes(..., reader=read_cached_or_current_overlay)` accepts the exact named immutable input reader. Ordinary use reads the declared repository path. This parameter does not change identity checks or synthesize canonical objects.

## Public reader

Save the complete Python API blocks from S19 through S24 READMEs outside the repository as `s19_evidence.py` through `s24_evidence.py`. Set `s24_evidence.ROOT` to the checkout (or an exact bounded input view) before the first call, using a fresh Python process for a changed view. The inherited [S23 reader](../s23-evidence/README.md) and its S19–S22 dependencies remain available. The [I52/I53 complete section recipe](../s23-evidence/navigation-repair-verification-I52.md) is unchanged.

`resource('I28')` returns the exact original JSON bytes. `at('I28', '/canonical_current_numbered_bindings/27')` returns35.29's original binding. `resolve({'document':'I28','json_pointer':'/original_byte_map/0'})` checks the original document identity. `span('source-I28-original', [425487,426629])` and `unit('35.29')` return the same complete1142 bytes. `recover()` returns the complete pre-I28 source. `section(anchor)` returns the whole original report section through the next equal/higher heading, including descendants; [navigation.json](navigation.json) lists every public anchor.

`resource('s23:source-composed-I51')` and inherited `s22:`, `s21:`, `s20:`, `s19:` prefixes retain their complete named historical versions. [Parent preservation](parent-contract-preservation.json) binds the exact old bytes of both changed S23 contracts. Ordinary `file()` always means the entire named physical file.

```python
"""S24 fixed-byte evidence API; all mathematical programs remain inert text."""
from pathlib import Path
from functools import lru_cache
from s19_evidence import strict_json, pointer
from s20_evidence import identity, interval
import s23_evidence as parent

ROOT = Path('.')
BASE = 'docs/reports/quantized-gh/s24-evidence/'

def file(path):
    p = Path(path)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError('repository-relative physical path required')
    return (ROOT / p).read_bytes()

@lru_cache(None)
def read_json(path):
    return strict_json(file(path))

def catalog():
    return read_json(BASE + 'composition.json')

def check(data, expected):
    return parent.check(data, expected)

def read_parts(name):
    entry = catalog()['versions'][name]
    descriptor = read_json(entry['descriptor'])
    if descriptor['schema'] != 's24-evidence-entry-v1' or descriptor['resource'] != name:
        raise ValueError('wrong resource descriptor')
    if descriptor['original'] != entry['identity']:
        raise ValueError('descriptor identity differs')
    chunks, cursor, line = [], 0, 1
    for ordinal, part in enumerate(descriptor['parts'], 1):
        data = check(file(part['path']), part)
        if not data or part['ordinal'] != ordinal or part['lines'] > 750:
            raise ValueError('empty, unordered or oversized raw part')
        if part['byte_span'] != [cursor, cursor + len(data)]:
            raise ValueError('part byte gap or overlap')
        if part['line_span'] != [line, line + part['lines'] - 1]:
            raise ValueError('part line coverage differs')
        if ordinal < len(descriptor['parts']) and not data.endswith(b'\n'):
            raise ValueError('interior part must end at LF')
        chunks.append(data)
        cursor += len(data)
        line += part['lf']
    return check(b''.join(chunks), descriptor['original'])

@lru_cache(None)
def resource(name):
    c = catalog()
    name = c['aliases'].get(name, name)
    if name.startswith(('s23:', 's22:', 's21:', 's20:', 's19:')):
        parent.ROOT = ROOT
        return parent.resource(name[4:] if name.startswith('s23:') else name)
    entry = c['versions'][name]
    kind = entry['kind']
    if kind == 'parts':
        data = read_parts(name)
    elif kind == 'file':
        data = file(entry['path'])
    elif kind == 'file_span':
        data = interval(file(entry['path']), entry['byte_span'])
    elif kind == 'slices':
        data = b''.join(interval(resource(s['version']), s['byte_span']) for s in entry['slices'])
    elif kind == 'i28_inverse':
        data = recover()
    else:
        raise ValueError('unknown S24 representation kind')
    return check(data, entry['identity'])

def at(name, json_pointer=''):
    return pointer(strict_json(resource(name)), json_pointer.removeprefix('#'))

def resolve(reference, owner='I54'):
    if owner == 'I54':
        binding = catalog()['immutable_documents'][reference['document']]
        data = check(resource(binding['path']), binding)
        return pointer(strict_json(data), reference['json_pointer'].removeprefix('#'))
    if owner == 'I28':
        return at('I28', reference if isinstance(reference, str) else reference['json_pointer'])
    if owner.startswith('s23:'):
        parent.ROOT = ROOT
        return parent.resolve(reference, owner[4:])
    raise ValueError('explicit declared owner required')

def span(version, byte_span, expected=None):
    data = interval(resource(version), byte_span)
    return check(data, expected) if expected is not None else data

def recover():
    """Apply all77 original I28 source/archive intervals, without rewriting them."""
    m = at('I28')
    chunks, cursor = [], 0
    for row in m['original_byte_map']:
        version = ('source-I28-original' if row['destination_path'] == catalog()['source_path']
                   else 'report-I28-original')
        data = span(version, [row['destination_start_byte'], row['destination_end_byte']], row)
        if [row['original_start_byte'], row['original_end_byte']] != [cursor, cursor + len(data)]:
            raise ValueError('original source gap or overlap')
        chunks.append(data)
        cursor += len(data)
    return check(b''.join(chunks), m['original_source'])

def section(anchor):
    nav = read_json(catalog()['navigation'])
    row = next(r for r in nav['report_sections'] if r['anchor'] == anchor)
    return span(nav['report_version'], row['byte_span'], row['identity'])

def unit(label):
    row = next(r for r in read_json(catalog()['current_units'])['units'] if r['label'] == label)
    return span('source-composed-I54', [row['span']['byte_start'], row['span']['byte_end_exclusive']], row['span'])

def canonical_record(atom_id, version='current'):
    """Historical paths are coordinates, never fabricated current physical aliases."""
    if version not in ('current', 'S23-original'):
        raise ValueError('explicit current or S23-original catalog required')
    row = next(r for r in read_json(catalog()['canonical_catalog'])['records'] if r['atom_id'] == atom_id)
    if version == 'S23-original' and row['origin'] == 'explicit-original-import':
        raise KeyError('S24 import absent from original S23 catalog')
    result = dict(row)
    if version == 'S23-original' and 'historical_yaml' in row:
        result['yaml'] = dict(row['historical_yaml'])
        result['coverage_gids'] = []
    return result

def canonical_bytes(atom_id, kind='cas', version='current', reader=None):
    if kind not in ('cas', 'yaml'):
        raise ValueError('cas or yaml required')
    row = canonical_record(atom_id, version)[kind]
    data = resource(row['version']) if 'version' in row else (reader or file)(row['path'])
    return check(data, row)

def verify():
    """Fixed representation checks only; no upstream global verify or program replay."""
    c = catalog()
    for name in c['versions']:
        resource(name)
    for alias, name in c['aliases'].items():
        if resource(alias) != resource(name):
            raise ValueError('alias differs')
    source = resource('source-composed-I54')
    if source != resource('source-S23-merged') + resource('tail-S24-I28'):
        raise ValueError('source concatenation differs')
    if resource('source-S23-merged') != resource('s23:source-composed-I51'):
        raise ValueError('original S23 prefix differs')
    units = read_json(c['current_units'])['units']
    regions = [(u['span']['byte_start'], u['span']['byte_end_exclusive'], u['span']) for u in units]
    regions += [(r['byte_span'][0], r['byte_span'][1], r['identity']) for r in c['structural_regions']]
    cursor = 0
    for start, end, expected in sorted(regions):
        if start != cursor:
            raise ValueError('source unit/structural gap or overlap')
        check(interval(source, [start, end]), expected)
        cursor = end
    if cursor != len(source):
        raise ValueError('source suffix uncovered')
    for row in read_json(c['own_addresses'])['addresses']:
        binding = resolve(row['binding_ref'])
        span(row['historical_version'], row['historical_span'], binding['original_numbered_span'])
        if not row['reserved']:
            current = span(row['current_version'], row['current_span'])
            if current != span('source-I28-original', row['original_I28_span']):
                raise ValueError('original whole unit differs')
    for row in read_json(BASE + 'original-consumers.json')['records']:
        at(row['owner'], row['pointer'])
        span(row['version'], row['byte_span'], row['identity'])
    for row in read_json(c['navigation'])['report_sections']:
        section(row['anchor'])
    for row in read_json(BASE + 'parent-contract-preservation.json')['parents']:
        check(resource(row['before_version']), row['before'])
        check(file(row['path']), row['current'])
    return dict(versions=len(c['versions']), aliases=len(c['aliases']), whole_units=len(units),
                structural_regions=len(c['structural_regions']), source=identity(source))
```

## Review and scientific limits

[Scientific scope](scientific-scope.json) preserves all original premises and limitations. Complete original S24 R2 results and wrappers are named resources in the catalog: architecture, quality and tests remain reject for the inherited mixed prefix. The separate original S23 R2 source approvals retain their disclosed unwaived method violations. Neither set is a fresh S24 vote. This candidate still requires complete source review, terminal formal intakes, caller-owned sealing, required CI and actual MERGED evidence.

Reasoning Discipline: exact byte identities and declared owners are the acceptance criteria; representation verification supplies no independent mathematical approval. Wider translated5040 and nonempty-S augmented completeness stay OPEN; the17 pending groups and PR6741 CLOSED/unmerged/neverreopen remain outside this layer.

[Published fixed representation checks](verification.json) include all commands, exits, errors and current intake method deviations. The [complete verification recipe](verification-recipe.md) and [changed-path identities](changed-paths.json) are public evidence.
