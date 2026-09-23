"""Exact balanced-profile head objective using the existing laminar Bellman solver."""
from fractions import Fraction as F
from hashlib import sha256
# Canonical report IO; all mathematical checks remain active under Python -O.
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/source-budgets/balanced_profile_head.json'
INPUT = 'frontier/source-budgets/balanced_profile_head_input.json'
LABEL_SOURCE = 'frontier/source-budgets/capped_head_bellman.py'
SOURCES = ('certificate_io.py', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md', 'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Probability.lean', '../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean', '../../../Library/Arith/schroeder2026noncoverage.md', '../../../Library/Arith/balister2018covering.md', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/depth_cap_bellman.py', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md')


def require(ok,message):
    if not ok:raise ValueError(message)

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable source module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_head_input(base):
    io = load_module('depth_profile_certificate_io', base/'certificate_io.py')
    record = json.loads(io.read_artifact_bytes(base/INPUT), object_pairs_hook=io._unique)
    require(set(record) == {'schema', 'head_label_source', 'head_label_factory',
                            'prime_order', 'heights', 'profiles'}, 'exact profile input fields')
    require(record['schema'] == 'depth-profile-head-input-v1', 'profile input schema')
    require(record['head_label_source'] == LABEL_SOURCE and
            record['head_label_factory'] == 'counterexample_154_labels', 'canonical literal head source')
    literal = load_module('depth_profile_original_labels', base/LABEL_SOURCE)
    labels = literal.counterexample_154_labels()
    require(len(labels) == 154, 'all 154 original labels retained')
    require(record['prime_order'] == [p for p in range(3, 74, 2) if literal.prime(p)],
            'all 20 odd head primes in numerical order')
    require(record['heights'] == [5, 3, 3, 2, 2, 2, 2] + [1]*13,
            'actual head prime-power heights')
    return io, record, labels


def calculate(base):
    io, record, labels = load_head_input(base)
    source_bytes={name:io.read_artifact_bytes(base/name) for name in SOURCES}
    profiles = tuple(tuple(F(r) for r in row) for row in record['profiles'])
    solver=load_module('balanced_existing_head_solver',base/'frontier/source-budgets/depth_cap_bellman.py')
    problem = solver.HeadProblem(record['prime_order'], record['heights'], labels, profiles)
    epsilon = problem.optimum()
    require(epsilon == F(39891291142993164384829733829906791483779,130822105133669014006347656250000000000000), 'exact balanced head value')
    require(epsilon < F(61,200), 'clean balanced head bound')
    result = dict(schema='balanced-profile-head-v1',
                  scope='Fixed literal 154-label head with the supplied depth profile; exact full-prefix-law head-union optimum. This memoization key does not discard actual sampled coordinates or future cofactor information.',
                  prime_order=record['prime_order'], heights=record['heights'],
                  profiles=record['profiles'], original_label_count=len(labels),
                  original_label_source=LABEL_SOURCE,
                  original_labels_sha256=hashlib.sha256(json.dumps(labels,separators=(',',':')).encode()).hexdigest(),
                  original_period=problem.period, epsilon_exact=str(epsilon),
                  states=problem.value.cache_info().currsize,
                  source_sha256={name:hashlib.sha256(raw).hexdigest() for name,raw in source_bytes.items()},
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    require(all(io.read_artifact_bytes(base/name)==raw for name,raw in source_bytes.items()),'head sources unchanged')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('balanced_output_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/balanced_profile_head.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact canonical balanced-profile replay')
    print(json.dumps({key:result[key] for key in ('schema', 'epsilon_exact', 'states')},indent=2))

if __name__=='__main__':
    main()
