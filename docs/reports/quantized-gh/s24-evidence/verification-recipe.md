# S24 fixed representation verification

Save the complete block outside the repository as `verify_s24.py`. Use an exact bounded current view whose inherited canonical paths come from the supplied cache and whose one covered-row overlay comes from the actual-predecessor capture. The original-inputs argument names the six complete supplied I28/pre-I28 bodies. The three phases are separate so a failed phase does not require replaying passed unrelated checks.

```sh
python3 -B verify_s24.py VIEW ORIGINAL_INPUTS representation representation.json
python3 -B verify_s24.py VIEW ORIGINAL_INPUTS canonical canonical.json
python3 -B verify_s24.py VIEW ORIGINAL_INPUTS consumers consumers.json
```

The script executes only the published fixed byte/JSON evidence APIs and the unchanged I53 text-section recipe. It does not execute any archived mathematical program or follow opaque references.

```python
"""Fixed S24 representation verification. No mathematical program is executed.
Usage: python3 -B verify_s24.py VIEW ORIGINAL_INPUTS PHASE OUTPUT_JSON
PHASE is representation, canonical, or consumers. VIEW supplies exact current
files with inherited canonical bodies from the named cache and current overlay.
"""
from pathlib import Path
import hashlib,json,re,sys,types

def identity(b):
    b.decode('utf-8')
    return dict(bytes=len(b),lf=b.count(b'\n'),terminal_lf=len(b)-len(b.rstrip(b'\n')),
                sha256=hashlib.sha256(b).hexdigest(),
                git_blob_oid=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())

def load(root):
    modules={}
    for stage in range(19,25):
        path=root/f'docs/reports/quantized-gh/s{stage}-evidence/README.md'
        blocks=re.findall(rb'^```python\n(.*?)^```[ \t]*$',path.read_bytes(),re.M|re.S)
        selected=[b for b in blocks if b.startswith(b'"""')]
        assert len(selected)==1,(stage,len(selected))
        name=f's{stage}_evidence';m=types.ModuleType(name);m.__file__=str(path);sys.modules[name]=m
        exec(compile(selected[0],str(path)+'#public-api','exec'),m.__dict__)
        if stage>=21:m.ROOT=root
        modules[stage]=m
    return modules

def representation(root,originals,modules):
    e=modules[24];result=e.verify()
    originals_by_name={'source-I28-original':'original-i28-source.md',
        'source-pre-I28-original':'original-pre-i28-source.md',
        'report-I28-original':'original-i28-report.md',
        'report-pre-I28-original':'original-pre-i28-report.md','I28-original':'original-i28-map.json',
        'tail-S24-I28':'owned-chapter35.md'}
    exact=[]
    for name,filename in originals_by_name.items():
        b=e.resource(name);assert b==(originals/filename).read_bytes();exact.append(dict(version=name,**identity(b)))
    c=e.catalog();m=e.at('I28');source=e.resource('source-composed-I54')
    assert identity(source)['sha256']=='9b73326f45cd654d6287ace8daf0a2e35c983d5912c67020036281ddb8b6eabe'
    assert (len(source),source.count(b'\n'))==(472616,9390)
    assert e.file(c['source_path'])==source
    old_parent=modules[23].resource('source-composed-I51')
    assert len(old_parent)==440285 and source[:440285]==old_parent
    assert modules[23].file(c['source_path'])==source
    assert [x['unit'] for x in e.read_json(c['own_addresses'])['addresses'] if x['reserved']]==['35.28','35.30']
    assert len(e.unit('35.29'))==1142
    assert e.unit('35.29')==e.span('source-I28-original',[425487,426629])
    boundary=e.read_json(e.BASE+'source-boundaries.json')['original_boundary']
    assert e.span('source-I28-original',boundary['old_34_22'],boundary['old_34_22_identity'])[-2:]==b'\n\n'
    result.update(exact_originals=exact,owned_units=28,original_inverse_segments=len(m['original_byte_map']),
                  original_consumer_records=len(e.read_json(e.BASE+'original-consumers.json')['records']),
                  zero_separator=True,ordinary_file_is_entire_current_source=True)
    return result

def canonical(root,originals,modules):
    e=modules[24];c=e.catalog();rows=e.read_json(c['canonical_catalog'])['records'];byid={r['atom_id']:r for r in rows}
    assert len(rows)==len(byid)==586
    bodies={};receipts={};checked=[]
    for row in rows:
        a=row['atom_id'];b=e.canonical_bytes(a);y=e.canonical_bytes(a,'yaml');bodies[a]=b;receipts[a]=y
        assert hashlib.sha256(b).hexdigest()==a
        text=y.decode()
        for prefix in ['  raw_sha256: sha256:','  normalized_sha256: sha256:','cas_ref: sha256:']:
            assert prefix+a+'\n' in text
        ordered=re.findall(r'^    - ([0-9a-f]{64})$',text,re.M)
        assert ordered==row['ordered_chain_atoms']
        assert ('  chain_atoms:\n' in text)==bool(ordered)
        assert '  unresolved_subitems: []\n' in text
        if row['coverage_gids']:
            assert a=='28df2a866cf2599b3db54e34a9b48622ab51e31ddcc65c6494f6335459d7b223'
            for edge in row['coverage_gids']:assert edge['gid'] in text and edge['target_statement_id'] in text
            assert '/absorbed-closed/' in row['yaml']['path']
        else:assert 'coverage_gids: []\n' in text
        checked.append(dict(atom_id=a,cas=identity(b),yaml=identity(y),chain_atoms=ordered))
    roots=[];chain_records=[]
    for u in e.read_json(c['current_units'])['units']:
        b=e.span('source-composed-I54',[u['span']['byte_start'],u['span']['byte_end_exclusive']],u['span'])
        assert b==bodies[u['atom_id']];roots.append(u['atom_id'])
    for row in rows:
        ids=row['ordered_chain_atoms']
        if ids:
            assert b''.join(bodies[a] for a in ids)==bodies[row['atom_id']]
            cursor=0;children=[]
            for a in ids:
                children.append(dict(atom_id=a,parent_byte_span=[cursor,cursor+len(bodies[a])],identity=identity(bodies[a])));cursor+=len(bodies[a])
            chain_records.append(dict(parent=row['atom_id'],children=children))
    reached=set()
    def visit(a,active):
        assert a not in active and a in byid
        if a in reached:return
        reached.add(a)
        for child in byid[a]['ordered_chain_atoms']:visit(child,active|{a})
    for a in roots:visit(a,set())
    closure=e.read_json(c['canonical_closure'])
    assert roots==closure['whole_unit_roots'] and sorted(reached)==closure['current_reachable']
    assert sorted(set(byid)-reached)==closure['retained_historical_only']
    assert (len(roots),len(reached),len(byid)-len(reached),len(chain_records))==(373,502,84,54)
    a='6e2fc9eba12f69ff66c2479b4effa34ffdfebf6d02465cf14009d3094f749a29';ids=byid[a]['ordered_chain_atoms']
    assert [len(bodies[x]) for x in ids]==[1006,136] and len(bodies[a])==1142
    moved='28df2a866cf2599b3db54e34a9b48622ab51e31ddcc65c6494f6335459d7b223'
    historical=e.canonical_bytes(moved,'yaml','S23-original');assert len(historical)==328
    assert e.canonical_record(moved,'S23-original')['coverage_gids']==[]
    assert len(e.canonical_bytes(moved,'yaml'))==489
    assert not (root/e.read_json(e.BASE+'upstream-covered-row.json')['original_path']).exists()
    imports=e.read_json(e.BASE+'imports.json')['records'];assert len(imports)==122
    for row in imports:
        b=(root/row['path']).read_bytes();obs=identity(b)
        assert obs['git_blob_oid']==row['original_oid'] and obs['sha256']==row['sha256']
        assert format((root/row['path']).stat().st_mode&0o177777,'06o')==row['new_mode']
    return dict(whole_units=373,retained_pairs=586,reachable_pairs=502,historical_only_pairs=84,
                chain_count=54,canonical_records=checked,ordered_chains=chain_records,
                imports=122,ingests=0,upstream_historical_row=identity(historical),
                upstream_current_row=identity(receipts[moved]),inherited_physical_checkout_reads=0)

def consumers(root,originals,modules):
    e19=modules[19].Evidence(root);e20=modules[20].S20Evidence(root,e19);result={};named=[];sections=[]
    # Explicitly omit CI and supporting-attempt resource bodies; no referents are followed.
    for n in list(e19.catalog['resources'])+list(e19.catalog['versions']):
        if n.startswith('CI-'):continue
        b=e19.raw(n);named.append(dict(api='S19.raw',name=n,identity=identity(b)))
    for alias,name in e19.catalog['aliases'].items():
        if name.startswith('CI-'):continue
        assert e19.raw(alias)==e19.raw(name)
    result['S19_spans']=e19.verify_spans();result['S19_references']=e19.verify_references()
    for row in json.loads((root/'docs/reports/quantized-gh/s19-evidence/navigation.json').read_bytes())['sections']:
        b=e19.section(row['anchor']);assert b==e19.raw('report')[row['start']:row['end']]
        sections.append(dict(api='S19.section',anchor=row['anchor'],identity=identity(b)))
    for n in e20.composition['versions']:
        b=e20.raw(n);named.append(dict(api='S20.raw',name=n,identity=identity(b)))
    for alias,name in e20.composition['aliases'].items():assert e20.raw(alias)==e20.raw(name)
    for stage in [21,22,23]:
        mod=modules[stage]
        for n in mod.catalog()['versions']:
            if n.startswith(('original-I44-','original-S22-')):continue
            b=mod.resource(n);named.append(dict(api=f'S{stage}.resource',name=n,identity=identity(b)))
        for alias,name in mod.catalog()['aliases'].items():assert mod.resource(alias)==mod.resource(name)
    for stage in [20,21,22,23,24]:
        mod=modules[stage];nav=json.loads((root/f'docs/reports/quantized-gh/s{stage}-evidence/navigation.json').read_bytes())
        for row in nav['report_sections']:
            b=e20.section(row['anchor']) if stage==20 else mod.section(row['anchor'])
            report=e20.raw(nav['report_version']) if stage==20 else mod.resource(nav['report_version'])
            assert b==report[row['byte_span'][0]:row['byte_span'][1]]
            sections.append(dict(api=f'S{stage}.section',anchor=row['anchor'],identity=identity(b)))
            for alias in row.get('aliases',[]):assert mod.section(alias)==b
    # Concrete original at/resolve/span consumers across distinct historical schemas.
    assert e19.resolve({'map':'I36','pointer':'/canonical/whole_source_units/0'},'I42')==e19.at('I36','/canonical/whole_source_units/0')
    assert e20.at('I29','/original_byte_partition/0')==e20.json('I29')['original_byte_partition'][0]
    ref={'document':'I32','json_pointer':'/original_units/0'}
    assert modules[21].resolve(ref)==modules[21].at('I32','/original_units/0')
    ref={'document':'I30','json_pointer':'/original_source_coverage/0'}
    assert modules[22].resolve(ref)==modules[22].at('I30','/original_source_coverage/0')
    ref={'document':'I44','json_pointer':'/current_bindings/1'}
    assert modules[23].resolve(ref)==modules[23].at('I44','/current_bindings/1')
    e24=modules[24];ref={'document':'I28','json_pointer':'/canonical_current_numbered_bindings/27'}
    assert e24.resolve(ref)==e24.at('I28',ref['json_pointer'])
    original_index=json.loads((root/'docs/reports/quantized-gh/s23-evidence/indexes/original-consumers-001.json').read_bytes())['records'];count=0
    for row in original_index:
        if 'version' in row:
            modules[23].at('I44',row['pointer']);modules[23].span(row['version'],row['byte_span'],{'sha256':row['sha256']});count+=1
    # Run the unchanged complete I53 fixed-text public section recipe, not a mathematical certificate.
    path=root/'docs/reports/quantized-gh/s23-evidence/navigation-repair-verification-I52.md'
    blocks=re.findall(rb'^```python\n(.*?)^```[ \t]*$',path.read_bytes(),re.M|re.S);assert len(blocks)==1
    assert hashlib.sha256(blocks[0]).hexdigest()=='1c9fd967dd44c0558c3cc2c96d8869ce0983d6068e296f2936f4eda9aa697aa1'
    ns={'__name__':'s24_fixed_section_recipe'};exec(compile(blocks[0],str(path)+'#complete-public-recipe','exec'),ns);ns['main'](root)
    result.update(named_versions=named,full_sections=sections,S23_original_consumer_records=count,
                  I53_recipe_sha256=hashlib.sha256(blocks[0]).hexdigest(),
                  omitted_resource_families=['CI-*','original-I44-* supporting result/audit','original-S22-* prior lifecycle results'],
                  omission_reason='Explicit input exclusions; these unchanged resources are not traversed by the changed source/version consumers.')
    return result

if __name__=='__main__':
    root=Path(sys.argv[1]);originals=Path(sys.argv[2]);phase=sys.argv[3];output=Path(sys.argv[4]);mods=load(root)
    result=globals()[phase](root,originals,mods);result['phase']=phase;result['result']='PASS'
    output.write_text(json.dumps(result,ensure_ascii=False,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if not isinstance(v,list)},ensure_ascii=False))
```
