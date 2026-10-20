import hashlib
import json
from pathlib import Path

ROOT = Path('/Users/macstudio/omega/trureturing-01a124be-current-residue-20261020')
EVIDENCE = Path('/Users/macstudio/omega/research/voa-string-01a124be/checkpoint-native-bpz-restoration-20261015/current-residue-negative-kernel-implementation-20261020')
A = EVIDENCE / 'acceptance'
ATTEMPT = Path('/Users/macstudio/.sshx/6ad77857bf296b386dff0153/attempt-1')
BASE = 'b187f9550ec4596b7f2fe620fdc8723547abeaa2'
D5 = 'D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue'
REG = 'Reg.' + D5
TARGETS = D5 + ' ' + REG


def load(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


hashes = load(EVIDENCE / 'source-hashes.json')
for rel, item in hashes.items():
    assert sha(ROOT / rel) == item['sha256']
    assert sha(Path(item['evidence_path'])) == item['sha256']

stmt = load(A / 'exact-statement-and-axioms.json')
reg = load(A / 'reg-binding-evidence.json')
inventory = load(A / 'declaration-consumers.json')
frozen_path = 'Golden/Frozen/state/D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.lean.json'
frozen = load(ROOT / frozen_path)
report = load(A / 'negative-current-scoped.json')
mods = {m['module']: m for m in report['modules']}
assert frozen['declarations'] == [
    {'declaration_name_key': d['name_key'], 'kind': d['kind']}
    for d in mods[D5]['declarations'] if d['include_in_statement']]

d5_cmd = "LEAN_NUM_THREADS=1 make lean LEAN_TARGETS='" + D5 + "'"
both_cmd = "LEAN_NUM_THREADS=1 make lean LEAN_TARGETS='" + TARGETS + "'"
commands = [
    {'command': d5_cmd, 'attempts': list(range(1, 20)), 'exit_codes': [2] * 19,
     'result': 'Normal clonefile cache admission rejected a busy main-checkout cache before compilation; subsequently resolved through the same entry.'},
    {'command': d5_cmd, 'attempts': [20, 21, 22], 'exit_codes': [2, 2, 0],
     'result': 'Attempt 20 seeded normally by clonefile; Lean elaboration/tactic errors in attempts 20 and 21 were corrected in the delivered source. Attempt 22 compiled the complete endpoint.'},
    {'command': both_cmd, 'attempt_family': 'Reg implementation', 'attempts': [1, 2, 3, 4],
     'exit_codes': [2, 2, 2, 0],
     'result': 'Concrete Reg probe elaboration/normalization errors were corrected; all retained D5 and Reg source compiles.'},
    {'command': "LEAN_NUM_THREADS=1 make lean-report-scoped LEAN_TARGETS='" + TARGETS +
                "' LEAN_REPORT='" + str(ROOT / '.current-residue/acceptance/negative-current-scoped.json') + "'",
     'exit_code': 0, 'result': 'Current exact-statement, axiom-closure and Reg binding report for two explicit roots and their import dependencies.'},
    {'command': "LEAN_NUM_THREADS=1 make emit PATHS='" + str(ROOT / '.current-residue/emit-paths.nul') + "'",
     'exit_code': 0, 'result': 'Canonical Scribe source compiled and Markdown emitted; manifest selects only the new document.'},
    {'command': "LEAN_NUM_THREADS=1 TMPDIR='" + str(ROOT / '.current-residue/tmp') +
                "' make deposit-uncovered BASE=" + BASE +
                ' GID=D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.singleton_negative_current_residue',
     'exit_code': 0, 'result': 'Scoped report, protected-base header check, canonical emit and canonical Frozen writer completed; no atom coverage claimed.'},
    {'command': both_cmd, 'attempt_family': 'final normal target verification', 'exit_code': 0,
     'result': 'Both normal mathematical and mirrored Reg roots build on the final unchanged source.'},
    {'command': 'make search-atoms', 'exit_code': 2,
     'result': 'Missing required SOURCE selector; not evidence of an atom search.'},
    {'command': 'make search-atoms SOURCE=D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.lean',
     'exit_code': 2, 'result': 'Source selector count=0; not a successful global atom search. Dispatcher supplied no atom, and deposit-uncovered reports NO_ATOM.'},
    {'command': 'python3 .current-residue/assemble-evidence.py', 'exit_codes': [1, 0],
     'result': 'An initial diagnostic incorrectly equated the report type identity with the material file byte hash. Packaging now records both separately and preserves the producer bytes; no Lean, report or judge source changed.'},
    {'command': 'GIT_OPTIONAL_LOCKS=0 git diff --exit-code ' + BASE + ' -- D5 Golden/Frozen Blueprint Reg tools .github',
     'exit_code': 0, 'result': 'No pre-existing tracked source/proof/Frozen/judge bytes changed; the delivery consists only of five new formalization files and local temporary diagnostics.'},
    {'command': 'GIT_OPTIONAL_LOCKS=0 git diff --check', 'exit_code': 0},
]

verification = {
    'stage': 'implementation',
    'mathematical_step': 'complete negative-current residue convolution on arbitrary actual native fields',
    'worktree': str(ROOT), 'base': BASE,
    'branch': 'lane/math/current-residue-negative-kernel-01a124be-20261020',
    'git_common_dir': '/Users/macstudio/omega/trureturing/.git',
    'source_hashes': hashes, 'commands': commands,
    'normal_build_exit_code': 0, 'scoped_report_exit_code': 0,
    'report': str(A / 'negative-current-scoped.json'),
    'report_sha256': sha(A / 'negative-current-scoped.json'),
    'statement': stmt['statement_text'], 'endpoint_identity': stmt['endpoint'],
    'standard_axioms': stmt['all_selected_root_axioms'], 'nonstandard_axioms': [],
    'scribe': {'source': hashes['Blueprint/D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.scribe.cs'],
               'canonical_emit_exit_code': 0, 'rendered_mirror_checked': True},
    'frozen': {'path': str(ROOT / frozen_path), 'state': frozen,
               'canonical_writer_exit_code': 0, 'declarations_match_current_report': True,
               'historical_frozen_keys_unchanged': True},
    'reg': reg, 'declaration_inventory': str(A / 'declaration-consumers.json'),
    'full_programme_complete': False,
}
write(EVIDENCE / 'verification.json', verification)

artifact_manifest = {}
for path in sorted(A.iterdir()):
    if path.is_file():
        artifact_manifest[str(path)] = {'sha256': sha(path), 'bytes': path.stat().st_size}
artifact_manifest[str(EVIDENCE / 'source-hashes.json')] = {'sha256': sha(EVIDENCE / 'source-hashes.json')}
artifact_manifest[str(EVIDENCE / 'verification.json')] = {'sha256': sha(EVIDENCE / 'verification.json')}

conclusion = {
    'stage': 'implementation',
    'implementation_status': 'exact negative convolution kernel-verified; Scribe/Frozen written; Reg binding audit unresolved',
    'original_full_goal_preserved': True,
    'full_programme_complete': False,
    'mathematical_result': {
        'module': D5,
        'theorem': stmt['endpoint']['name'],
        'exact_statement': stmt['statement_text'],
        'statement_id': stmt['endpoint']['statement_id'],
        'type_sha256': stmt['endpoint']['type_sha256'],
        'source_sha256': mods[D5]['source_sha256'],
        'quantification': 'Arbitrary D,hu,index,F:NativeField D hu,gamma:Int,k:Int,x:ActualTensor D hu. No desired-law, locality, Ward, insertion, Jacobi or module-law premise.',
        'ordered_residue_definition': stmt['ordered_residue_definition'],
        'both_ordered_supports': [d for d in stmt['all_authored_D5_statements']
                                 if d['name'].endswith(('current_residue_left_finite', 'current_residue_right_finite'))],
        'proof': [
            'The left ordered natural-index support follows from the actual Hahn order of F(x); the right follows from actual current truncation at x.',
            'For every j<m, negative_residue_modes reindexes both ordered residues to the same K(q): A(q)(B(k-m-q)x) for q<0, B(k-m-q)(A(q)x) for q>=0.',
            'Missing negative prefixes vanish by Nat.choose_eq_zero_of_lt; the integer outer sign is retained and proved. Actual seed order and current truncation give a finite q interval.',
            'Finite Vandermonde in this actual current consumer gives sum_j choose(-1/2,j)*choose(-q-1,m-1-j)=choose(-q-3/2,m-1), exactly jetScalar index.2 q.',
            'Public wordField_coefficient and flatTerm_finite identify the actual singleton coefficient. The signed exponent comparison is exact, and m=1 is included.',
        ],
        'admission_basis': 'escape-witness',
        'escape_witness': 'The consumed negative_residue_modes proof identifies two actual ordered residue sums with one finite normal coefficient, including signed reindexing and vanishing binomial prefixes; the actual coefficient endpoint consumes it and finite Vandermonde.',
        'source_faithfulness': 'No new field/evaluator construction, basis-only restriction, scalar-only replacement or assumed desired law.',
        'hypothesis_inhabitance_evidence': 'The compiled Reg hyperbolic lattice has determinant -1, an actual nonzero charged ground tensor, a nonzero creation coefficient and a nonzero singleton coefficient. Its probes prove actual observational dependence and are audit evidence, not a restriction on the universal D5 theorem.',
        'public_supplier_reuse': str(A / 'reused-frozen-declarations.json'),
    },
    'verification': {
        'normal_targets': [D5, REG], 'final_normal_build_exit_code': 0,
        'scoped_report_exit_code': 0, 'scoped_report': str(A / 'negative-current-scoped.json'),
        'scoped_report_sha256': sha(A / 'negative-current-scoped.json'),
        'scope': 'Two explicit genuine changed roots and their import/utility closure; no whole-repository report or CI claim.',
        'standard_axioms': stmt['all_selected_root_axioms'],
        'nonstandard_axioms': [], 'sorryAx': False,
        'exact_statement_evidence': str(A / 'exact-statement-and-axioms.json'),
        'exact_compiled_type_materials': str(A / 'new-d5-statement-materials.zip'),
        'command_results_including_failures': commands,
        'resource_route': 'Guarded normal make entries, LEAN_NUM_THREADS=1, existing omega-gate 8 GiB admission and LeanEval priority. Normal clonefile donor eventually admitted; no independent dependency download or bypass.',
    },
    'scribe_and_frozen': verification['scribe'] | {'frozen': verification['frozen']},
    'reg_outcome': {
        'source': hashes['Reg/D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.lean'],
        'kernel_build_exit_code': 0,
        'faithful_attempt': 'Three full-source dependent families with Iff.rfl exact source bridges, actual-positive laws, rejected-family variation, single-readout sensitivity and actual nonzero observational dependence, using typed enrolled DependentFamily.realize and continuation unknown.',
        'registration_complete': False, 'declared_validated_count': 0,
        'records': reg['records'],
        'common_failure': {'code': 'IE-C050', 'name': 'ClosedTruthReadout',
                           'reason': 'unclassified_form', 'rule': 'source.dictionary_or_proof_coordinate',
                           'site': '', 'readout': '', 'state': 'declared_unresolved', 'certificate': None},
        'missing_evidence': 'Accepted source binding certificate / declared_validated four-slot registration for all three public theorems.',
        'issue_routing': reg['routing'],
        'judge_or_status_forced': False,
        'no_recursive_private_helper_audits': True,
    },
    'new_author_declarations': {
        group: [{k: d[k] for k in ['name', 'source_name', 'kind', 'visibility', 'consumers']}
                | ({'proof_shape': d['proof_shape']} if 'proof_shape' in d else {})
                | ({'external_consumer': d['external_consumer']} if d.get('external_consumer') else {})
                for d in inventory[group]] for group in ['D5', 'Reg']},
    'complete_declaration_inventory': str(A / 'declaration-consumers.json'),
    'source_hashes': hashes, 'acceptance_artifacts': artifact_manifest,
    'preservation_and_isolation': {
        'worktree': str(ROOT), 'base': BASE, 'common_git': '/Users/macstudio/omega/trureturing/.git',
        'preexisting_source_proof_private_names_and_frozen_keys_unchanged': True,
        'read_only_diff_exit_code': 0,
        'changed_paths': list(hashes),
        'only_additions': True, 'git_or_github_mutations': False,
        'same_round_peer_or_forbidden_root_reads': False,
        'prior_terminal_inputs_read_as_proposals_only': True,
        'opaque_log_refs_opened_hashed_copied_or_reinterpreted': False,
        'extra_workers_or_oracle_calls': False,
        'host_process_or_configuration_changes': False,
        'persistent_evidence_contains': 'Unique new substantive Lean/Scribe/Markdown/Frozen source, scoped report/provenance, focused statement materials, consumer inventory and binding diagnostics; no .lake/packages/full materials bundle/process transcripts.',
    },
    'remaining_diagnostics': [
        'All three Reg bindings are declared_unresolved with IE-C050 ClosedTruthReadout; an issue link is still caller-owned and not yet created.',
        'The source-name atom selector returned count=0 with exit 2, so no global no-atom search is claimed. The brief supplies no atom and the canonical writer used deposit-uncovered / NO_ATOM.',
        'Cache admission and local Lean/Reg elaboration failures were resolved; the final retained normal targets compile.',
    ],
    'caller_handoff': {
        'owner': 'orchestration caller',
        'next_actions': [
            'Open or reuse a CLAUDE §3.9 issue naming the three public theorems, exact IE-C050 diagnostics and missing binding certificates; link it in delivery.',
            'Dispatch independent CLI tests, quality and architecture reviews of the exact preserved source and resolve blocking findings without weakening the endpoint.',
            'Perform publication completeness and required CI checks, publish a small PR, obtain MERGED, synchronize dev and verify the integrated exact result.',
            'After publication/integration and no unique unpushed content, remove this worktree through the canonical worktree-remove target.',
        ],
        'worktree_retained': True,
        'reason': 'Worker is expressly prohibited from Git/GitHub mutations and caller owns publication/review/CI/dev synchronization/cleanup.',
        'full_current_iterate': 'Not proved: complete positive residue/correction, tail support and every-cutoff equality remain downstream obligations.',
        'arbitrary_state_twisted_jacobi': 'Not proved.',
        'full_moonshine_voa_cft_anomaly_fusion_string_ads_cft_programme': 'Unchanged and incomplete.',
    },
    'readable_verification': str(EVIDENCE / 'verification.json'),
}

# The sentinel is deliberately not written by this preparation script.
write(ROOT / '.current-residue/prepared-result.json', {
    'conclusion': conclusion,
    'log_ref': '/Users/macstudio/.sshx/6ad77857bf296b386dff0153/attempt-1/worker.stdout.log',
})
print(json.dumps({'prepared_result': str(ROOT / '.current-residue/prepared-result.json'),
                  'verification': str(EVIDENCE / 'verification.json'),
                  'D5_names': len(conclusion['new_author_declarations']['D5']),
                  'Reg_names': len(conclusion['new_author_declarations']['Reg']),
                  'result_bytes': (ROOT / '.current-residue/prepared-result.json').stat().st_size}))
