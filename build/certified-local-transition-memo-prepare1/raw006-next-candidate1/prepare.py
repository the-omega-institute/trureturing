"""Prepare Raw006's all-input factorization; never build or deploy.

--prepare writes only the small reusable module in this owned directory.
--check also dry-generates, but does not write, the full 128 Raw + 128 Response
consumer and the existing 392-receipt dictionary. --emit-consumer explicitly
writes those optional candidates here. The sparse dictionary is a correctness
candidate, not a measured improvement. --census reads the original source data.
"""

import argparse
import ast
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
PARENT = BASE.parent
EJM = 'D5/S3/Quantum/Entanglement/EJM/'
RAW = EJM + 'Frontier/Raw/Part000/PreparedEJMCompleteFrontierRaw006.lean'
MEMO = ('candidate/' + EJM + 'Frontier/Raw/Part000/Raw002Cap8/'
        'Raw293Sharing/MemoPilot125.lean')
NORMALIZED = EJM + 'EJMCertifiedNormalizedLocalTransitionMemo.lean'
DICTIONARY = EJM + 'Raw006Memo/SharedPilotLocalDictionary.lean'
DICTIONARY_MODULE = DICTIONARY[:-5].replace('/', '.')
DICTIONARY_NS = 'D5.S3.Quantum.Entanglement.EJM.Raw006Memo.SharedPilotLocalDictionary'
HEAD = '276e23e3c6556d941ea7b5d0b8af938ea8b7db31'
PINS = {
    RAW: 'ac1c8e9d2699dc4ef1809af1c1ef1c1e661fbccf2f51d830fc9e00fbe426c15e',
    EJM + 'PreparedEJMCompleteFrontierTypes.lean':
        '3e7afdf052d389b3241606d681c93a6f89bd35d7b5b3de84f2ce358e086ba225',
    EJM + 'EJMCacheState.lean':
        'dae7fa4bd347d8214340f5a7ed9e8ca59630f1f39bbcc8e4cab8291ba66c9695',
    EJM + 'EJMLocalCacheData.lean':
        'f6e894e2c4f648935e534f7840acc7a4129984cfbeaec765492e42a3da22d830',
    EJM + 'EJMOriginalReplayAssembly.lean':
        '20cf19c4aa67b1f9a825412451bc91e3578ba514fe0206e044a8c2c0a9aa44d1',
    EJM + 'EJMOriginalGlobalDAGData.lean':
        '71d413e1f03f018ea7ae8df423cc67bea83773577fccf1f57593ecee665553a7',
    'build/raw002-cap8-rebuild-prepare1/raw293-sharing-prepare1/prepare.py':
        '93908b2fe1d9357909d362f8ddd2e8cdc1d5fac25e0d5c65b7812bf76add8762',
    'build/full-original-hard-cost-prepare1/generate_hard_cost.py':
        '806e00b1fbbd1db6ecd960ad2707186f0887ef6cb00a10216333cddd0dbba1f6',
    'lean-toolchain': 'ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c',
    'lakefile.toml': '9fe9260b2b5287935cab3a5811f43dfcaf438563cc9c1d4922d46f50cd704d96',
    'lake-manifest.json': '8550e44937f85a9be196a2917a075eeb8c22bf6c15baa83e72017c6fc4437a8e',
}
PARENT_PINS = {
    'candidate/D5/S0/Certificates/CertifiedLocalTransitionMemo.lean':
        '681d5024c375263159f9a277defe88393c252809057a335b5d8f4dd5d3326668',
    'candidate/' + EJM + 'EJMCertifiedLocalTransitionMemo.lean':
        '3cd1e8738015c0dccc5bad80300593726bb84dfbe9996428bf7727ada3487bbd',
    MEMO: '904da1d49b19926aa52295b46946004b6bde2d9fad8519f875ccb4d950df76e0',
}
RAW_PATTERN = (r'theorem (raw_cut_(\d{5})) : '
    r'EJMOriginalReplayAssembly.Accepted (\d+) (\d+) ⟨(\d+), by decide⟩ := by\n'
    r'  unfold EJMOriginalReplayAssembly.Accepted\n  decide \+kernel')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_inputs():
    git = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()
    assert git('rev-parse', 'HEAD') == HEAD
    assert git('rev-parse', '--path-format=absolute', '--git-common-dir') == \
        '/Users/macstudio/omega/trureturing/.git'
    for relative, expected in PINS.items():
        assert sha(ROOT / relative) == expected, relative
    for relative, expected in PARENT_PINS.items():
        assert sha(PARENT / relative) == expected, relative


def sparse_dictionary():
    memo = (PARENT / MEMO).read_text()
    local = memo[memo.index('def triangleLocal000 :'):memo.index('def cache000 : Cache :=')]
    assert 'Accepted' not in local
    assert len(re.findall(r'^def certified_(?:triangle|singleton)_', local, re.M)) == 392
    return '''/- Prepared receipt-only dictionary, not an accepted Raw theorem.
   Source data are copied exactly from the pinned MemoPilot125 local segment.
   Its existing 392 entries cover only 0.504% of Raw006 suffix local calls;
   this dictionary does not establish or promise a cost improvement. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper
import D5.S3.Quantum.Entanglement.EJM.CanonicalCacheStateEqualityCandidate
import D5.S3.Quantum.Entanglement.EJM.EJMCertifiedLocalTransitionMemo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ''' + DICTIONARY_NS + '''
open EJMCacheState (CachedLocal triangleStep singletonStep)
open Tail442V2.Helper (FullLocalFields cachedLocal_eq_of_fields)
open EJMCertifiedLocalTransitionMemo
  (LocalInput TriangleReceipt SingletonReceipt triangleReceipt singletonReceipt)

''' + local + '\nend ' + DICTIONARY_NS + '\n'


def consumer(dictionary_module, triangle_lookup, singleton_lookup):
    original = (ROOT / RAW).read_text()
    def replace(match):
        name, _, depth, code, index = match.groups()
        return (f'theorem {name} : EJMOriginalReplayAssembly.Accepted '
            f'{depth} {code} ⟨{index}, by decide⟩ := by\n'
            '  apply (EJMCertifiedNormalizedLocalTransitionMemo.accepted_iff_memo\n'
            f'    {triangle_lookup}\n    {singleton_lookup}\n'
            f'    {depth} {code} ⟨{index}, by decide⟩).2\n'
            '  decide +kernel')
    source, count = re.subn(RAW_PATTERN, replace, original)
    assert count == 128
    source = source.replace('import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes',
        'import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes\n'
        'import D5.S3.Quantum.Entanglement.EJM.EJMCertifiedNormalizedLocalTransitionMemo\n'
        'import ' + dictionary_module, 1)
    source = ('''/- Optional complete Raw006 candidate. No kernel or resource result.
   All original 128 Accepted statements and 128 Response definitions remain.
   Only prefix/suffix transition evaluation is transported by all-input proofs.
   Original packed DAG nodes, all value branches, fuel, full partial assignment,
   lower, scale and symmetry tests are unchanged. -/
''' + source)
    statement = r'^theorem raw_cut_\d{5} : (.*?) := by$'
    assert re.findall(statement, source, re.M) == re.findall(statement, original, re.M)
    response = r'^theorem response_cut_\d{5} : .*?\n  response_of_raw[^\n]+'
    assert re.findall(response, source, re.M) == re.findall(response, original, re.M)
    assert len(re.findall(r'^theorem raw_cut_', source, re.M)) == 128
    assert len(re.findall(r'^theorem response_cut_', source, re.M)) == 128
    assert not re.search(r'^import .*PreparedEJMCompleteFrontierRaw006\s*$', source, re.M)
    assert not re.search(r'^import .*MemoPilot125\s*$', source, re.M)
    return source


def census():
    reader_path = ROOT / 'build/raw002-cap8-rebuild-prepare1/raw293-sharing-prepare1/prepare.py'
    spec = importlib.util.spec_from_file_location('raw006_original_source_reader', reader_path)
    reader = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reader)
    data = reader.ExactData()
    record = data.census(reader.roots(ROOT / RAW))
    memo = (PARENT / MEMO).read_text()
    literal_pattern = (r'def ((?:triangle|singleton)Local\d{3}) : CachedLocal \d+ :=\n'
        r'  ⟨\((\d+), \((\d+), (\d+)\)\), ⟨(\d+), \((-?\d+)\), '
        r'(0x[0-9a-f]+), (0x[0-9a-f]+)⟩⟩')
    literals = {name: tuple(int(value, 0) for value in values)
        for name, *values in re.findall(literal_pattern, memo)}
    old_keys = [set(), set()]
    for label, before, i, a in re.findall(r'theorem (triangle|singleton)_update_\d{3} :\n'
        r'    (?:triangleStep|singletonStep) (\w+) \(⟨(\d+), by decide⟩ : Fin \d+\) ⟨(\d+), by decide⟩', memo):
        old_keys[label == 'singleton'].add((literals[before], int(i), int(a)))
    blocks = []
    for bid, label in enumerate(['triangle', 'singleton']):
        calls = record['calls'][bid]
        normalized, mirrors = Counter(), Counter()
        for (state, i, a), count in calls.items():
            q = data.blocks[bid]['perm'][data.inverse[state[1]]][i]
            actual = data.outcomes[state[2]][a]
            normalized[(state[5], state[6], q, actual)] += count
            next_state = record['examples'][bid][state, i, a][2]
            mirrors[next_state[0]] += count
        blocks.append(dict(kind=label, suffixLocalCalls=sum(calls.values()), fullNineFieldKeys=len(calls),
            existingDictionaryUsed=len(set(calls) & old_keys[bid]),
            existingDictionaryHits=sum(calls[key] for key in old_keys[bid]),
            normalizedPackedKeys=len(normalized), outputMirrorKeys=len(mirrors),
            normalizedTopHits={str(n): sum(count for _, count in normalized.most_common(n))
                for n in [16, 64, 128, 512]},
            mirrorTopHits={str(n): sum(count for _, count in mirrors.most_common(n))
                for n in [16, 64, 128, 512]}))
    return dict(nativeSourceCensusOnly=True, kernelAcceptance=None, resourceAcceptance=None,
        rawStatements=128, originalResponses=128, originalContexts=record['contexts'],
        nodeKinds=dict(record['kinds']), uniqueFuelNodes=record['uniqueFuelNodes'], blocks=blocks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--prepare', action='store_true')
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--emit-consumer', action='store_true')
    mode.add_argument('--census', action='store_true')
    parser.add_argument('--dictionary-module')
    parser.add_argument('--triangle-lookup')
    parser.add_argument('--singleton-lookup')
    args = parser.parse_args()
    supplied = [args.dictionary_module, args.triangle_lookup, args.singleton_lookup]
    assert all(supplied) or not any(supplied), 'Supply all three dictionary arguments together'
    for value in filter(None, supplied):
        assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', value)
    verify_inputs()
    if args.census:
        print(json.dumps(census(), indent=2))
        return
    normalized = (BASE / 'templates/EJMCertifiedNormalizedLocalTransitionMemo.lean').read_text()
    source = consumer(args.dictionary_module or DICTIONARY_MODULE,
        args.triangle_lookup or DICTIONARY_NS + '.triangleLookup',
        args.singleton_lookup or DICTIONARY_NS + '.singletonLookup')
    dictionary = sparse_dictionary() if not any(supplied) else None
    assert not re.search(r'^\s*(axiom|unsafe|opaque)\b|\bsorry\b', normalized, re.M)
    output = BASE / 'candidate' / NORMALIZED
    if args.prepare or args.emit_consumer:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(normalized)
    assert output.read_text() == normalized
    if args.emit_consumer:
        raw_output = BASE / 'candidate' / RAW
        raw_output.parent.mkdir(parents=True, exist_ok=True)
        raw_output.write_text(source)
        if dictionary is not None:
            dictionary_output = BASE / 'candidate' / DICTIONARY
            dictionary_output.parent.mkdir(parents=True, exist_ok=True)
            dictionary_output.write_text(dictionary)
    ast.parse(Path(__file__).read_text())
    print(json.dumps(dict(preparedOnly=True, LeanExecuted=False, deployed=False,
        smallReusableModule=str(output.relative_to(BASE)), normalizedSHA256=sha(output),
        dryGeneratedRawStatements=128, dryGeneratedOriginalResponses=128,
        consumerWritten=args.emit_consumer,
        optionalConsumerBytes=len(source.encode()),
        optionalDictionaryBytes=len(dictionary.encode()) if dictionary is not None else None,
        kernelAcceptance=None, resourceAcceptance=None)))


if __name__ == '__main__':
    main()
