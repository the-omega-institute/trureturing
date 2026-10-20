import hashlib
import json
import re
import shutil
import subprocess
import zipfile
from pathlib import Path

ROOT = Path('/Users/macstudio/omega/trureturing-01a124be-current-residue-20261020')
EVIDENCE = Path('/Users/macstudio/omega/research/voa-string-01a124be/checkpoint-native-bpz-restoration-20261015/current-residue-negative-kernel-implementation-20261020')
BASE = 'b187f9550ec4596b7f2fe620fdc8723547abeaa2'
MODULE = 'D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue'
REG_MODULE = 'Reg.' + MODULE
NS = 'D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField'
REPORT = ROOT / '.current-residue/acceptance/negative-current-scoped.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


report = json.loads(REPORT.read_text())
mods = {m['module']: m for m in report['modules']}
selected = [mods[MODULE], mods[REG_MODULE]]
for m in selected:
    assert sha(ROOT / m['source_path']) == m['source_sha256'].removeprefix('sha256:')
    assert all(set(d['axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
               for d in m['declarations'])

stem = 'S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue'
paths = ['D5/' + stem + '.lean', 'Reg/D5/' + stem + '.lean',
         'Blueprint/D5/' + stem + '.scribe.cs', 'Blueprint/D5/' + stem + '.md',
         'Golden/Frozen/state/D5/' + stem + '.lean.json']
hashes = {}
for rel in paths:
    src = ROOT / rel
    assert src.is_file(), rel
    dst = EVIDENCE / 'source' / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    if not dst.exists() or sha(dst) != sha(src):
        shutil.copyfile(src, dst)
    hashes[rel] = {'sha256': sha(src), 'evidence_path': str(dst)}
write_json(EVIDENCE / 'source-hashes.json', hashes)

acceptance = EVIDENCE / 'acceptance'
acceptance.mkdir(exist_ok=True)
for suffix in ['', '.provenance.json', '.input.attestation', '.sha256']:
    shutil.copyfile(Path(str(REPORT) + suffix), acceptance / (REPORT.name + suffix))

author_d5 = [d for d in mods[MODULE]['declarations'] if d['include_in_statement']]
assert len(author_d5) == 9
material_index = []
with zipfile.ZipFile(str(REPORT) + '.materials.zip') as src, zipfile.ZipFile(
        acceptance / 'new-d5-statement-materials.zip', 'w', zipfile.ZIP_DEFLATED) as dst:
    for d in author_d5:
        key = d['type_sha256'].replace('sha256:', 'sha256/')
        data = src.read(key)
        dst.writestr(key, data)
        material_index.append({**d, 'material_path': key, 'bytes': len(data),
                               'material_bytes_sha256': hashlib.sha256(data).hexdigest()})
    dst.writestr('index.json', json.dumps(material_index, indent=2) + '\n')

consumer_map = {
    'currentResidue': ['negative_residue_modes', 'singleton_negative_current_residue'],
    'current_residue_left_finite': ['negative_residue_modes', 'Reg.Left.familyRegistration'],
    'current_residue_right_finite': ['negative_residue_modes', 'Reg.Right.familyRegistration'],
    'normalKernel': ['normalKernel_finite', 'negative_residue_modes', 'singleton_negative_current_residue'],
    'normalKernel_finite': ['negative_residue_modes', 'singleton_negative_current_residue'],
    'reindex_supported_nat': ['negative_residue_modes'],
    'negative_residue_modes': ['singleton_negative_current_residue'],
    'jet_vandermonde': ['singleton_negative_current_residue'],
    'singleton_negative_current_residue': ['Reg.probe_singleton', 'Reg.Convolution.rejected_law', 'Reg.Convolution.familyRegistration'],
}
shapes = {
    'currentResidue': 'definition', 'normalKernel': 'definition',
    'current_residue_left_finite': 'content', 'current_residue_right_finite': 'bind-only',
    'normalKernel_finite': 'content', 'reindex_supported_nat': 'bind-only',
    'negative_residue_modes': 'content', 'jet_vandermonde': 'bind-only',
    'singleton_negative_current_residue': 'content',
}
d5_inventory = []
for d in author_d5:
    short = d['name'].split('.')[-1]
    d5_inventory.append({**d, 'source_name': short,
                         'visibility': 'private' if d['name'].startswith('_private.') else 'public',
                         'proof_shape': shapes[short], 'consumers': consumer_map[short]})

common_consumers = {
    'hyperbolic': ['hyperbolic_unit', 'probeGround', 'probeState', 'probeExcited', 'probeSeed'],
    'hyperbolic_unit': ['probeGround', 'probeState', 'probeExcited', 'probeSeed', 'Left.dependence', 'Right.dependence', 'Convolution.dependence'],
    'probeGround': ['probeGround_nonzero', 'probeState', 'probeExcited', 'probe_leading', 'probeState_nonzero'],
    'probeGround_nonzero': ['probe_leading', 'probeState_nonzero'],
    'probeState': ['probe_leading', 'probe_negative', 'probe_singleton', 'probeState_nonzero', 'repeated_not_finite', 'Left.dependence', 'Convolution.dependence'],
    'probeExcited': ['probe_excited_annihilation', 'Right.dependence'],
    'probeSeed': ['probe_leading', 'probe_negative', 'probe_singleton', 'Left.dependence', 'Right.dependence', 'Convolution.dependence'],
    'probe_leading': ['probe_creation_nonzero', 'Right.dependence'],
    'probe_negative': ['probe_singleton'],
    'creation_injective': ['probe_creation_nonzero'],
    'probe_creation_nonzero': ['Left.dependence', 'Convolution.dependence'],
    'probe_current_nonnegative': ['probe_singleton'],
    'probe_excited_annihilation': ['Right.dependence'],
    'probe_singleton': ['Convolution.dependence'],
    'probeState_nonzero': ['repeated_not_finite', 'Convolution.rejected_law'],
    'ResidueParameter': ['Left.signature', 'Left.arena', 'Right.signature', 'Right.arena'],
    'repeated_not_finite': ['Left.rejected_law', 'Right.rejected_law'],
    'CoefficientParameter': ['Convolution.signature', 'Convolution.arena'],
}
for stage in ['Left', 'Right', 'Convolution']:
    for name, consumers in {
        'signature': ['actual', 'rejected', 'arena', 'dependence', 'registration'],
        'actual': ['source_bridge', 'dependence', 'familyRegistration', 'registration'],
        'rejected': ['rejected_law', 'familyRegistration'],
        'arena': ['source_bridge', 'rejected_law', 'familyRegistration', 'registration'],
        'source_bridge': ['familyRegistration'],
        'rejected_law': ['familyRegistration'],
        'dependence': ['familyRegistration'],
        'familyRegistration': ['registration'],
        'registration': [],
    }.items():
        common_consumers[stage + '.' + name] = [stage + '.' + c for c in consumers]

reg_inventory = []
stage = None
reg_text = (ROOT / ('Reg/D5/' + stem + '.lean')).read_text()
for line_no, line in enumerate(reg_text.splitlines(), 1):
    match = re.fullmatch(r'namespace (Left|Right|Convolution)', line)
    if match:
        stage = match.group(1)
    if line in ['end Left', 'end Right', 'end Convolution']:
        stage = None
    match = re.match(r'(?:(private) )?(abbrev|def|theorem|structure) (\w+)', line)
    if not match:
        continue
    private, kind, name = match.groups()
    rel = (stage + '.' if stage else '') + name
    suffix = REG_MODULE + '.' + rel
    candidates = [d for d in mods[REG_MODULE]['declarations'] if d['name'] == suffix or
                  (d['name'].startswith('_private.') and d['name'].endswith('.' + suffix))]
    assert len(candidates) == 1, (rel, len(candidates))
    reg_inventory.append({**candidates[0], 'source_name': rel, 'source_line': line_no,
                          'source_kind': kind, 'visibility': 'private' if private else 'public',
                          'consumers': [REG_MODULE + '.' + c for c in common_consumers[rel]],
                          'external_consumer': 'typed registration discovery in the current scoped report'
                          if rel.endswith('.registration') else None})
assert len(reg_inventory) == 45
d5_names = {d['source_name']: d['name'] for d in d5_inventory}
reg_names = {d['source_name']: d['name'] for d in reg_inventory}
for d in d5_inventory:
    d['consumers'] = [reg_names[c.removeprefix('Reg.')] if c.startswith('Reg.')
                      else d5_names[c] for c in d['consumers']]
for d in reg_inventory:
    d['consumers'] = [reg_names[c.removeprefix(REG_MODULE + '.')]
                      for c in d['consumers']]
write_json(acceptance / 'declaration-consumers.json',
           {'D5': d5_inventory, 'Reg': reg_inventory,
            'scope': 'Author-written declarations; compiler-generated declarations remain in the canonical report.'})

records = mods[REG_MODULE]['information_templates']['records']
assert len(records) == 3
assert all(r['state'] == 'declared_unresolved' and r['certificate'] is None for r in records)
write_json(acceptance / 'reg-binding-evidence.json', {
    'module': REG_MODULE, 'source_sha256': mods[REG_MODULE]['source_sha256'],
    'records': records, 'registration_complete': False,
    'routing': {
        'owner': 'caller', 'authority': 'CLAUDE.md §3.9; explicit implementation brief',
        'action': 'Open or reuse an issue for all three original public theorems before publication and link it in delivery.',
        'missing_evidence': 'Accepted source binding certificate / declared_validated four-slot records.',
        'issue_url': None,
        'issue_not_created_reason': 'The implementation worker is prohibited from Git/GitHub mutations.',
        'judge_modified': False,
    },
})

statement = (ROOT / ('D5/' + stem + '.lean')).read_text()
start = statement.index('theorem singleton_negative_current_residue')
stop = statement.index(' := by', start)
statement = statement[start:stop]
endpoint = next(d for d in author_d5 if d['name'] == NS + '.singleton_negative_current_residue')
write_json(acceptance / 'exact-statement-and-axioms.json', {
    'module': MODULE, 'source_sha256': mods[MODULE]['source_sha256'],
    'statement_text': statement, 'endpoint': endpoint,
    'ordered_residue_definition': (ROOT / ('D5/' + stem + '.lean')).read_text().split('def currentResidue',1)[1].split('\n/- proof_shape:',1)[0],
    'all_authored_D5_statements': author_d5,
    'all_selected_root_axioms': sorted({ax for m in selected for d in m['declarations'] for ax in d['axioms']}),
    'nonstandard_axioms': [], 'sorryAx': False,
    'exact_type_materials': str(acceptance / 'new-d5-statement-materials.zip'),
    'evidence_source': 'Canonical guarded scoped Lean report, including compiled proof axiom closures.',
})

frozen_dependencies = []
wanted = {'tensor_current_truncation', 'wordField_coefficient', 'flatTerm_finite',
          'sourceWeight', 'singletonLinear', 'jetCurrent', 'jetScalar', 'halfBinomial'}
for m in report['modules']:
    for d in m['declarations']:
        if d['name'].split('.')[-1] in wanted:
            frozen_dependencies.append({'name': d['name'],
                                        'gid': m['source_path'].removesuffix('.lean') + '.' + d['name'].split('.')[-1],
                                        'statement_id': d['statement_id'],
                                        'frozen_state': 'Golden/Frozen/state/' + m['source_path'] + '.json'})
write_json(acceptance / 'reused-frozen-declarations.json', frozen_dependencies)

print(json.dumps({'sources': hashes, 'D5_authored': len(d5_inventory),
                  'Reg_authored': len(reg_inventory), 'scoped_report_sha256': sha(REPORT),
                  'statement_materials_bytes': (acceptance / 'new-d5-statement-materials.zip').stat().st_size}, indent=2))
