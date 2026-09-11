# I50 fixed representation check code

These are the complete current byte, JSON, schema and navigation checks used by I50. They import only the published S19/S20/S21/S22 evidence APIs, copied to external scratch. They execute no historical mathematical code or certificate. The exact original supplied inputs and immutable S21 cache are required at the declared paths. Original programs inside recovered reports remain inert text.

The API check invoked `Evidence(ROOT).verify()`, `S20Evidence(ROOT, evidence).verify()`, `s21_evidence.verify()` and `s22_evidence.verify()` after complete code reading. Its original outputs and all observed checker failures are retained in the implementation result. The final S22 source representation receives a fresh S22 consumption check after its storage change. Passing inherited checks are not repeated without a relevant edit or failure.

## Canonical, original-owner and inherited consumer checks

Command: `PYTHONPATH=/tmp/qgh-i50-composition-work-0911 python3 -B /tmp/qgh-i50-composition-work-0911/audit.py`

```python
"""Current byte/schema/navigation checks only. No historical mathematics runs."""
from pathlib import Path
import hashlib, json, re, subprocess, zipfile
import s21_evidence as s21
import s22_evidence as s22
from s19_evidence import strict_json, pointer, Evidence
from s20_evidence import S20Evidence, interval

ROOT=Path('/Users/auricstudio/trureturing-qgh-pure-s22')
WORK=Path('/tmp/qgh-i50-composition-work-0911')
INPUT=Path('/tmp/qgh-boundaries-0908/s22-composition-i50-inputs-0911')
BASE='docs/reports/quantized-gh/s22-evidence/'
HEAD='5253e57794449c11746721449f8acfd0a2c5e9dd'
s21.ROOT=ROOT;s22.ROOT=ROOT

def ident(b):
    return dict(bytes=len(b),lf=b.count(b'\n'),lines=b.count(b'\n')+int(bool(b) and not b.endswith(b'\n')),
        terminal_lf=len(b)-len(b.rstrip(b'\n')),sha256=hashlib.sha256(b).hexdigest(),
        git_blob_oid=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())

def read(path):return (ROOT/path).read_bytes()
def js(path):return strict_json(read(path))
def equal(a,b,label):
    if a!=b:raise ValueError(label)

result={}
c=s22.catalog();source=s22.resource('source-composed-I50');m=s22.at('I30')
recovery={}
for name,filename in [('source-S21-merged','merged-s21-source.md'),('source-I30-current','original-i30-source.md'),
    ('source-original-pre-I30','original-pre-i30-source.md'),('report-I30-current','original-i30-report.md'),
    ('report-original-pre-I30','original-pre-i30-report.md'),('I30','original-i30-map.json'),
    ('tail-S22-I30','s22-owned-pure-tail.md'),('source-composed-I50','expected-composed-source.md')]:
    b=s22.resource(name);equal(b,(INPUT/filename).read_bytes(),name);recovery[name]=ident(b)
result['original_and_composed_recovery']=recovery

# Exhaustive original-map consumers retain their original ownership and schema.
current=s22.resource('source-I30-current');original=s22.resource('source-original-pre-I30')
report=s22.resource('report-I30-current');partition=[];archives=[]
for i,row in enumerate(m['original_source_coverage']):
    a,b=row['original_span'];x,y=row['destination_span']
    data=s22.span('source-I30-current' if row['destination']=='source' else 'report-I30-current',[x,y],row)
    equal(data,interval(original,[a,b]),'original coverage '+str(i))
    if row['destination']=='source':partition.append((x,y))
    else:archives.append(dict(index=i,original_span=[a,b],report_span=[x,y],identity=ident(data)))
for row in m['source_additions']:
    a,b=row['current_span'];equal(interval(current,[a,b]),row['text'].encode(),'addition bytes');partition.append((a,b))
cursor=0
for a,b in sorted(partition):equal(a,cursor,'original I30 output partition');cursor=b
equal(cursor,len(current),'original I30 output EOF')
for row in m['canonical']['complete_current_numbered_bindings']:
    data=s22.span('source-I30-current',row['current_span'],row['identity'])
    equal(hashlib.sha256(data).hexdigest(),Path(row['cas_path']).name,'original map whole binding')
    equal(row['actual_yaml_structure']['cas_ref'],'sha256:'+row['identity']['sha256'],'original map cas ref')
for row in m['canonical']['historical_terminal_lf_relations']:
    assert row['exact_relation']=='longer_bytes == predecessor_bytes + one LF'
    assert row['predecessor_cas_ref'].startswith('sha256:') and row['longer_cas_ref'].startswith('sha256:')
for row in m['canonical']['historical_chain_structures']:
    assert isinstance(row['ordered_chain_atom_ids'],list) and row['ordered_chain_concatenation_equals_parent'] is True
for row in m['canonical']['changed_paths']:
    assert isinstance(row['path'],str)
    if row['git_status']==' D':
        assert isinstance(row['historical_identity'],dict)
    elif 'identity' in row:
        assert isinstance(row['identity'],dict)
    else:
        assert row['identity_placement']=='final envelope avoids self-referential mapping/report hashes'
result['I30_original_consumers']=dict(coverage_spans=56,output_partition_spans=len(partition),additions=30,
    numbered_correspondences=22,original_current_numbered_bindings=208,archives=archives,
    historical_lf_metadata_records=15,historical_chain_metadata_records=22,historical_changed_path_records=42,
    historical_mathematical_checks_replayed=0)

# Only named immutable cached canonical resources and the explicit increment are read.
archive=Path('/tmp/qgh-boundaries-0908/s21-full-composed-review-dispatch-r3-0911.zip')
ab=archive.read_bytes();equal(len(ab),12904245,'cache size')
equal(hashlib.sha256(ab).hexdigest(),'61f9b2a412d5d0056009ca981f8ce87c1e8d91da89761659f455e06506457703','cache hash')
z=zipfile.ZipFile(archive);equal(len(z.namelist()),2339,'cache members')
aliases=strict_json(z.read('candidate-paths.json'))['paths'];manifest=strict_json(z.read('manifest.json'))['members']
records={r['atom_id']:r for r in js('docs/reports/quantized-gh/s20-evidence/canonical-pairs.json')['pairs']}
for atom,row in js('docs/reports/quantized-gh/s21-evidence/canonical-pairs.json')['tail_pairs'].items():
    assert atom not in records
    records[atom]=dict(atom_id=atom,cas=dict(path=row['cas_path'],**row['cas_identity']),yaml=dict(path=row['yaml_path'],**row['yaml_identity']))
equal(len(records),452,'inherited retained count')
for row in js(BASE+'canonical-pairs.json')['tail_pairs']:
    assert row['atom_id'] not in records;records[row['atom_id']]=row
imports={r['path']:r for r in js(BASE+'imports.json')['records']}
cas={};chains={};resources=[]
for atom,row in records.items():
    parts={}
    for kind in ('cas','yaml'):
        e=row[kind];path=e['path']
        if path in imports:
            b=read(path);equal(ident(b)['git_blob_oid'],imports[path]['original_oid'],'import exact OID');origin='explicit-original-increment'
        else:
            member=aliases[path]
            assert '/Meta/Digestion/' in member and not any(t in member.lower() for t in ('worker','diagnostic','transcript','peer-result'))
            b=z.read(member);s22.check(b,manifest[member]);origin=member
        s22.check(b,e);parts[kind]=b;resources.append(dict(path=path,origin=origin,identity=ident(b)))
    equal(ident(parts['cas'])['sha256'],atom,'CAS address')
    text=parts['yaml'].decode();base=('fingerprints:\n  raw_sha256: sha256:'+atom+'\n  normalized_sha256: sha256:'+atom+
        '\ncas_ref: sha256:'+atom+'\ncoverage_gids: []\nreceipts:\n  unresolved_subitems: []\n')
    assert text.startswith(base),(atom,'YAML header shape')
    tail=text[len(base):]
    if tail:
        assert re.fullmatch(r'  chain_atoms:\n(?:    - [0-9a-f]{64}\n)+\n?',tail),(atom,'YAML chain shape')
        chains[atom]=re.findall(r'^    - ([0-9a-f]{64})$',tail,re.M)
    cas[atom]=parts['cas']
for parent,children in chains.items():equal(b''.join(cas[x] for x in children),cas[parent],'ordered parent chain '+parent)
units=js(c['current_units'])['units']
for u in units:
    span=u['span'];equal(interval(source,[span['byte_start'],span['byte_end_exclusive']]),cas[u['atom_id']],'whole current unit')
def closure(roots):
    reached=set();pending=list(roots)
    while pending:
        atom=pending.pop()
        if atom in reached:continue
        assert atom in records;reached.add(atom);pending.extend(chains.get(atom,[]))
    return reached
old=closure(u['atom_id'] for u in units[:304]);now=closure(u['atom_id'] for u in units)
equal(len(old),431,'S21 roots');equal(len(now),450,'S22 roots');equal(len(records),494,'retained catalog');equal(len(chains),53,'parent chains')
result['canonical']=dict(current_whole_units=323,current_roots=sorted(u['atom_id'] for u in units),
    inherited_root_reachable_count=len(old),current_root_reachable_count=len(now),retained_catalog_count=len(records),
    historical_only=sorted(set(records)-now),ordered_parent_chains=chains,resources=resources,
    inherited_physical_canonical_reads=0,explicit_import_paths=len(imports),ingest=0)

# Real inherited document, binding and span consumers; archived code remains inert.
maps={n:s21.at(n) for n in ('I32','I35','I37')};reference_count=0
def walk(value):
    if isinstance(value,dict):
        yield value
        for v in value.values():yield from walk(v)
    elif isinstance(value,list):
        for v in value:yield from walk(v)
for row in walk(maps['I37']):
    if set(('document','json_pointer'))<=row.keys():
        s21.resolve(row);reference_count+=1
for row in js('docs/reports/quantized-gh/s21-evidence/own-addresses.json')['addresses']:
    ref=row['binding_ref']
    # The composition address catalog uses named-map pointers, including I37 itself.
    # I37's immutable_documents resolver is for its external I32/I35 references only.
    binding=s21.at(ref['document'],ref['json_pointer']);reference_count+=1
    if row['reserved']:s21.span('source-pre-I32',binding['source_span'])
    else:
        equal(s22.span('source-S21-merged',row['current_span']),s22.span('s21:source-I37-original',row['historical_span']),'S21 address')
for name,owner in [('original_canonical_bindings','source-pre-I32'),('current_canonical_bindings','source-I32-current')]:
    for row in maps['I32'][name]:s21.span(owner,row['source_span'])
indexes={'historical_binding_ref':{r['atom_id'] for r in maps['I32']['original_canonical_bindings']},
         'canonical_binding_ref':{r['atom_id'] for r in maps['I32']['current_canonical_bindings']},
         'pair_ref':{r['atom_id'] for r in maps['I32']['new_canonical_pairs']}}
for row in walk(maps['I32']):
    for key,values in indexes.items():
        if key in row:assert row[key] in values;reference_count+=1
for row in walk(maps['I35']['current_unit_bindings']):
    for key in ('full_parent_ref','pair_ref'):
        if key in row and row[key] is not None:assert row[key] in maps['I35']['canonical_catalog'];reference_count+=1
for row in maps['I35']['current_unit_bindings']:s21.span('source-I35-current',row['source_span'])
equal(s21.recover('I35','/recovery_partitions/pre_I32_source/segments'),s21.resource('source-pre-I32'),'second original I32 recovery')
change=maps['I37']['representation_change']
for k in ('old_table','old_proof'):s21.span('source-I35-current',change[k])
for k in ('new_array','current_proof'):s21.span('source-I37-original',change[k])
stored=s21.span('report-I35-current',maps['I35']['report_evidence_spans']['verifier_result'])
stored=strict_json(stored)
for row in change['row_bindings']:
    pointer(stored,row['stored_result_json_pointer']);reference_count+=1
    s21.span('source-I35-current',row['original_source_coordinates'])
    s21.span('source-I37-original',row['current_source_coordinates'])
result['inherited_consumers']=dict(actual_document_and_binding_references=reference_count,
    sixteen_original_and_current_row_spans=16,whole_support_proof_bytes=992,
    original_I32_second_recovery=True,ordinary_file_semantics='Unchanged',
    fixed_source_bounds=dict(S19=[0,337429],S20=[0,364059],S21=[0,394734]))

for row in js(BASE+'parent-contract-preservation.json')['changes']:
    b=read(row['archive']);s22.check(b,row['identity'])
    equal(b,subprocess.check_output(['git','cat-file','blob',HEAD+':'+row['path']],cwd=ROOT),'before contract bytes')
result['parent_before_archives']=js(BASE+'parent-contract-preservation.json')['changes']
(WORK/'representation-audit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(dict(recovery_versions=len(recovery),I30_original_bindings=208,current_units=323,
    retained_records=len(records),current_reachable=len(now),chains=len(chains),inherited_references=reference_count),ensure_ascii=False))
```

## Public navigation and aliases

Command: `PYTHONPATH=/tmp/qgh-i50-composition-work-0911 python3 -B /tmp/qgh-i50-composition-work-0911/navigation.py`

```python
"""Fixed public link, navigation and declared-resource checks; archived code is inert."""
from pathlib import Path
import json, re, urllib.parse
from s19_evidence import Evidence
from s20_evidence import S20Evidence
import s21_evidence as s21
import s22_evidence as s22

ROOT=Path('/Users/auricstudio/trureturing-qgh-pure-s22')
WORK=Path('/tmp/qgh-i50-composition-work-0911')
s21.ROOT=ROOT;s22.ROOT=ROOT

def visible(text):
    rows=[];fence=None
    for line in text.splitlines():
        m=re.match(r'^\s{0,3}(`{3,}|~{3,})',line)
        if m:
            mark=m.group(1)
            if fence is None:fence=mark
            elif mark[0]==fence[0] and len(mark)>=len(fence):fence=None
        elif fence is None:rows.append(line)
    return '\n'.join(rows)

def anchors(text):
    text=visible(text);result=set(re.findall(r'<a\s+(?:id|name)=["\']([^"\']+)',text));seen={}
    for title in re.findall(r'^#{1,6} +(.+?)\s*$',text,re.M):
        title=re.sub(r'\[([^\]]+)\]\([^)]*\)',r'\1',title)
        slug=re.sub(r'[^\w\- ]','',title.lower()).replace(' ','-')
        n=seen.get(slug,0);seen[slug]=n+1
        result.add(slug+('-'+str(n) if n else ''))
    return result

docs=['docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md']
docs += ['docs/reports/quantized-gh/'+n for n in ('balanced-prime-235-all-slabs-0910.md',
    'balanced-prime-237-all-slabs-0910.md','actual-5040-fixed-box-0910.md','actual-5040-density-order-0910.md')]
docs += ['docs/reports/quantized-gh/'+n+'-evidence/README.md' for n in ('s19','s20','s21','s22')]
links=[]
for path in docs:
    text=visible((ROOT/path).read_text())
    # Remove inline code so mathematical tuples and API examples are not links.
    text=re.sub(r'`+[^`]*`+','',text)
    for target in re.findall(r'\[[^\]\n]*\]\(([^\s]+?)\)',text):
        url=urllib.parse.urlsplit(target)
        if url.scheme or target.startswith('//'):continue
        if not ('/' in url.path or '.' in url.path or url.fragment):continue
        dest=((ROOT/path).parent/urllib.parse.unquote(url.path)).resolve() if url.path else ROOT/path
        assert dest.is_relative_to(ROOT),(path,target,'outside repository')
        assert dest.is_file(),(path,target,'missing local target')
        if url.fragment:
            assert urllib.parse.unquote(url.fragment) in anchors(dest.read_text()),(path,target,'missing fragment')
        links.append(dict(owner=path,target=target,resolved=str(dest.relative_to(ROOT)),fragment=url.fragment))

e19=Evidence(ROOT);e20=S20Evidence(ROOT,e19);declared=[]
for alias,name in e19.catalog['aliases'].items():
    assert e19.raw(alias)==e19.raw(name);declared.append('s19:'+alias)
for alias,name in e20.composition['aliases'].items():
    assert e20.raw(alias)==e20.raw(name);declared.append('s20:'+alias)
for name in s21.catalog()['inherited_resources']:
    s21.resource(name);declared.append('s21:'+name)
nav19=json.loads((ROOT/'docs/reports/quantized-gh/s19-evidence/navigation.json').read_bytes())
for row in nav19['sections']:
    e19.section(row['anchor'])
    assert row['anchor'] in anchors((ROOT/'docs/reports/quantized-gh/balanced-prime-235-all-slabs-0910.md').read_text())

# Every declared inherited current-unit map pointer remains usable through the public API.
count=0
for row in json.loads((ROOT/'docs/reports/quantized-gh/s21-evidence/current-units.json').read_bytes())['units']:
    if row.get('inherited_pointer') is not None:
        ref=row['inherited_pointer'];s21.at(ref['map'],ref['pointer']);count+=1
for stage in ('s21','s22'):
    base='docs/reports/quantized-gh/'+stage+'-evidence/'
    nav=json.loads((ROOT/(base+'navigation.json')).read_bytes())
    report='docs/reports/quantized-gh/actual-5040-'+('fixed-box' if stage=='s21' else 'density-order')+'-0910.md'
    found=anchors((ROOT/report).read_text())
    for row in nav['report_sections']:
        assert row['anchor'] in found
        assert all(a in found for a in row['aliases'])
        a,b=row['byte_span']
        descriptor=json.loads((ROOT/(base+('report-I37-original' if stage=='s21' else 'report-I30-current')+'.json')).read_bytes())
        expected=[p['path'] for p in descriptor['parts'] if p['byte_span'][0]<b and p['byte_span'][1]>a]
        assert row['parts']==expected
        for path in row['parts']:assert (ROOT/path).is_file()

for n in ('33.20','33.21','33.22'):
    assert n in anchors((ROOT/'docs/reports/quantized-gh/actual-5040-density-order-0910.md').read_text())
    assert not re.search(rb'^\*\*'+n.encode().replace(b'.',rb'\.')+rb' ',(ROOT/docs[0]).read_bytes(),re.M)
result=dict(local_links=links,local_link_count=len(links),declared_aliases_and_inherited_resources=declared,
    S19_report_sections=251,S21_report_sections=30,S22_report_sections=10,
    inherited_current_unit_map_pointers=count,reserved_S22_addresses=['33.20','33.21','33.22'],
    archived_relative_link_owners='Original source/report paths explicitly preserved; raw parts have no new link base.',
    network_requests=0,opaque_references_followed=0)
(WORK/'navigation-audit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(dict(local_links=len(links),declared_resources=len(declared),inherited_unit_pointers=count),ensure_ascii=False))
```

## Final original-source representation consumption

Command: `PYTHONPATH=/tmp/qgh-i50-composition-work-0911 python3 -B /tmp/qgh-i50-composition-work-0911/final-consumption.py`

```python
"""Consume the final S22 representation after sharing the original prefix."""
from pathlib import Path
from functools import lru_cache
import hashlib, json, re
import s21_evidence as s21
import s22_evidence as s22

ROOT=Path('/Users/auricstudio/trureturing-qgh-pure-s22')
WORK=Path('/tmp/qgh-i50-composition-work-0911')
INPUT=Path('/tmp/qgh-boundaries-0908/s22-composition-i50-inputs-0911')
s21.ROOT=ROOT;s22.ROOT=ROOT
# The unchanged inherited resource bytes are memoized within this one fixed snapshot.
# The public API code and its ordinary whole-file semantics are unchanged.
s21.resource=lru_cache(maxsize=None)(s21.resource)
result=s22.verify()
for name,filename in [('source-I30-current','original-i30-source.md'),
                      ('source-original-pre-I30','original-pre-i30-source.md'),
                      ('report-I30-current','original-i30-report.md'),
                      ('report-original-pre-I30','original-pre-i30-report.md'),
                      ('source-S21-merged','merged-s21-source.md'),('I30','original-i30-map.json')]:
    assert s22.resource(name)==(INPUT/filename).read_bytes(),name
d=s22.read_json(s22.BASE+'source-I30-current.json');entry=s22.catalog()['versions']['source-I30-current']
assert d['original']==entry['identity'] and d['slices']==entry['slices']
assert d['origin']['git_blob_oid']=='0b6239f2af0100f3b863b4f6d291b98adb3daa42'
for stage in ('s19','s20','s21','s22'):
    text=(ROOT/('docs/reports/quantized-gh/'+stage+'-evidence/README.md')).read_text()
    blocks=re.findall(r'^```python\n(.*?)^```',text,re.M|re.S)
    code=next(b for b in blocks if ('class Evidence:' in b if stage=='s19' else
        'class S20Evidence:' in b if stage=='s20' else 'def resource(name):' in b))
    assert code.encode()==(WORK/(stage+'_evidence.py')).read_bytes(),stage
result['original_five_versions_and_map_exact']=True
result['shared_original_prefix_bytes']=343492
result['original_separator_bytes']=1
result['current_raw_parts']=sum(len(s22.read_json(v['descriptor'])['parts']) for v in s22.catalog()['versions'].values() if v['kind']=='parts')
result['public_API_code_exact']=True
result['new_source_descriptor_link_exists']=(ROOT/(s22.BASE+'source-I30-current.json')).is_file()
(WORK/'final-consumption.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False))
```

## Final capacities and exact changed paths

Command: `PYTHONPATH=/tmp/qgh-i50-composition-work-0911 python3 -B /tmp/qgh-i50-composition-work-0911/capacities.py`

```python
"""Exact current changed paths and capacities; no inherited canonical body scan."""
from pathlib import Path
import hashlib, json, subprocess

ROOT=Path('/Users/auricstudio/trureturing-qgh-pure-s22')
WORK=Path('/tmp/qgh-i50-composition-work-0911')
SOURCE='docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md'
BASE='docs/reports/quantized-gh/s22-evidence/'
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def ident(b):
    b.decode('utf-8')
    return dict(bytes=len(b),lf=b.count(b'\n'),lines=b.count(b'\n')+int(bool(b) and not b.endswith(b'\n')),
        terminal_lf=len(b)-len(b.rstrip(b'\n')),sha256=hashlib.sha256(b).hexdigest(),
        git_blob_oid=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())
assert git('rev-parse','HEAD').decode().strip()=='5253e57794449c11746721449f8acfd0a2c5e9dd'
assert git('branch','--show-current').decode().strip()=='lane/math/quantized-gh-composed-s22-0911'
assert git('diff','--cached','--name-only')==b''
tracked=[x.decode() for x in git('diff','--name-only','-z','HEAD').split(b'\0') if x]
assert set(tracked)=={SOURCE,'docs/reports/quantized-gh/s21-evidence/README.md','docs/reports/quantized-gh/s21-evidence/composition.json'}
new=[x.decode() for x in git('ls-files','--others','--exclude-standard','-z').split(b'\0') if x]
imports=json.loads((ROOT/(BASE+'imports.json')).read_bytes())['records'];allowed={x['path'] for x in imports}
public={'docs/reports/quantized-gh/actual-5040-density-order-0910.md','docs/reports/quantized-gh/theory-body-migration-s22-0910.json'}
assert all(p in allowed or p in public or p.startswith(BASE) for p in new)
assert allowed<=set(new)
records=[]
for path in sorted(tracked+new):
    p=ROOT/path;assert p.is_file() and not p.is_symlink()
    b=p.read_bytes();i=ident(b)
    if path!=SOURCE:assert i['lines']<=800,(path,i['lines'])
    if path.startswith(BASE+'raw/'):assert i['lines']<=750,(path,i['lines'])
    if path.endswith('.json'):json.loads(b)
    records.append(dict(path=path,status='modified' if path in tracked else 'added',identity=i))
dirs=[]
for p in [ROOT/BASE]+sorted((ROOT/BASE).rglob('*')):
    if p.is_dir():
        files=[x for x in p.iterdir() if x.is_file()]
        assert len(files)<=40,(str(p),len(files));dirs.append(dict(path=str(p.relative_to(ROOT)),direct_files=len(files)))
result=dict(changed_paths=records,changed_path_count=len(records),tracked_modified=len(tracked),added=len(new),
    exact_canonical_import_paths=len(allowed),new_directories=dirs,max_direct_files=max(x['direct_files'] for x in dirs),
    max_new_or_changed_evidence_lines=max(r['identity']['lines'] for r in records if r['path']!=SOURCE),
    max_raw_part_lines=max(r['identity']['lines'] for r in records if r['path'].startswith(BASE+'raw/')),
    source_explicit_8150_line_exception=True,index_unchanged=True,HEAD_unchanged=True,branch_unchanged=True)
(WORK/'capacities-and-paths.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('changed_paths','new_directories')},ensure_ascii=False))
```
