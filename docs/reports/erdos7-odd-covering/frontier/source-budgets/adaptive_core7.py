"""Exact adaptive core7 optimum and complete positive actual policy."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import argparse
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('adaptive_core_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/adaptive_core7.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    raw=ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(raw).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','locked literal input')
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    curve_raw=ctx.raw('certificates/source_norms/source-budgets/square_stoploss_curve.json')
    LIMIT_STATES=2_000_000;LIMIT_SECONDS=300;START=time.monotonic()
    primes, heights, labels = data['prime_order'], data['heights'], data['labels']
    rows = [[F(x) for x in r] for r in data['profiles']]
    require(primes[:7] == [3, 5, 7, 11, 13, 17, 19], 'declared seven core coordinates')
    require(len(primes) == len(heights) == len(rows) == 20, 'all twenty coordinates')
    require(len(labels) == len({m for m, a in labels}) == 154, 'literal distinct IDs')
    require(all(m > 1 and m % 2 and 0 <= a < m for m, a in labels), 'odd congruences')
    require(all(34 % m != a for m, a in labels), 'retained uncovered witness')
    units = [r[-1].denominator for r in rows]
    caps = [r[-1].numerator for r in rows]
    for p, h, row in zip(primes, heights, rows):
        require(row[0] == 1 and len(row) == h + 1, 'complete cap profiles')
        require(all(row[e] == p ** (h - e) * row[-1] for e in range(1, h + 1)),
                'flat complete leaf caps imply ancestor bounds')
        require(p ** h * row[-1] >= 1, 'normalized feasible leaf row')

    scopes = [sum(1 << i for i, p in enumerate(primes) if m % p == 0)
              for m, a in labels]
    core_only = [j for j, s in enumerate(scopes) if s < 128]
    terminal_ids = [[j for j, s in enumerate(scopes) if s >> i & 1]
                    for i in range(7, 20)]
    require(len(core_only) == 78 and sum(map(len, terminal_ids)) == 76 and
            all((s >> 7).bit_count() <= 1 for s in scopes), 'complete terminal geometry')
    require(all(h == 1 for h in heights[7:]), 'terminal depth one')
    complete = [sum(1 << j for j in core_only if not scopes[j] & u) for u in range(128)]
    terminal_den = prod(units[7:])
    den = [terminal_den * prod(units[i] for i in range(7) if u >> i & 1)
           for u in range(128)]
    leaf_groups = []
    for i in range(7):
        size = primes[i] ** heights[i]
        factors = [gcd(m, size) for m, a in labels]
        groups = Counter(sum(1 << j for j, ((m, a), g) in enumerate(zip(labels, factors))
                             if x % g == a % g) for x in range(size))
        leaf_groups.append(tuple(groups.items()))

    memo = {}
    choices = {}
    stats = dict(terminal_states=0, terminal_residue_checks=0, completed_states=0,
                 row_evaluations=0, grouped_leaf_evaluations=0, merged_groups=0,
                 absorbing_returns=0, empty_returns=0)
    root_values = {}


    class ResourceStop(Exception):
        pass


    def terminal(active):
        survival = 1
        for i, ids in enumerate(terminal_ids, 7):
            forbidden = {labels[j][1] % primes[i] for j in ids if active >> j & 1}
            survival *= min(units[i], caps[i] * (primes[i] - len(forbidden)))
            stats['terminal_residue_checks'] += len(ids)
        stats['terminal_states'] += 1
        require(0 <= survival <= terminal_den, 'terminal product is a probability')
        return terminal_den - survival


    def value(u, active):
        if active & complete[u]:
            stats['absorbing_returns'] += 1
            return den[u]
        if not active:
            stats['empty_returns'] += 1
            return 0
        key = (u, active)
        known = memo.get(key)
        if known is not None:
            return known
        if len(memo) % 1000 == 0:
            elapsed = time.monotonic() - START
            if len(memo) >= LIMIT_STATES or elapsed >= LIMIT_SECONDS:
                raise ResourceStop(f'{len(memo)} states at {elapsed:.3f} seconds')
        if u == 0:
            answer = terminal(active)
            axis = -1
        else:
            answer, axis = den[u] + 1, None
            for i in range(7):
                if not u >> i & 1:
                    continue
                groups = Counter()
                for mask, count in leaf_groups[i]:
                    groups[active & mask] += count
                stats['grouped_leaf_evaluations'] += len(leaf_groups[i])
                stats['merged_groups'] += len(groups)
                costs = sorted((value(u ^ (1 << i), child), child, count * caps[i])
                               for child, count in groups.items())
                remaining, total = units[i], 0
                for cost, child, available in costs:
                    mass = min(remaining, available)
                    total += mass * cost
                    remaining -= mass
                    if not remaining:
                        break
                require(remaining == 0 and 0 <= total <= den[u], 'normalized exact row')
                stats['row_evaluations'] += 1
                if total < answer:
                    answer, axis = total, i
                if u == 127 and active == (1 << 154) - 1:
                    root_values[str(primes[i])] = str(F(total, den[u]))
        memo[key] = answer
        choices[key] = axis
        return answer


    result = dict(schema='adaptive-core7-absorbing-boundary-exact-v1',
                  scope='Attained exact minimum over arbitrary full-history core7 coordinate selection, followed by the terminal13 coordinates, for the literal seven-phase154 head and unchanged balanced caps. No full20 interleaving optimum or arbitrary-phase conclusion.',
                  input_sha256=sha256(raw).hexdigest(),
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  state_limit=LIMIT_STATES, seconds_limit=LIMIT_SECONDS)
    numerator = value(127, (1 << 154) - 1)
    epsilon = F(numerator, den[127])
    fixed = F('159049786725785092501063718513057031733423/417584159586671492708261718750000000000000')
    require(epsilon <= fixed, 'fixed numerical schedule remains admissible')
    table_digest = sha256()
    for (u, active), val in sorted(memo.items()):
        line = json.dumps([u, str(active), str(val), choices[u, active]], separators=(',', ':')) + '\n'
        table_digest.update(line.encode())
    pending = [(127, (1 << 154) - 1)]
    visited, policy, terminals = set(), [], []
    by_depth = [Counter() for _ in range(7)]
    absorbing_edges = 0
    while pending:
        u, active = pending.pop()
        if (u, active) in visited:
            continue
        visited.add((u, active))
        require(not active & complete[u], 'expand only unresolved policy boundaries')
        if u == 0:
            terminals.append([str(active), str(memo[u, active])])
            continue
        val, i = memo[u, active], choices[u, active]
        require(u >> i & 1, 'read a remaining coordinate')
        child_u = u ^ (1 << i)
        groups = Counter()
        for mask, count in leaf_groups[i]:
            groups[active & mask] += count
        costs = sorted((den[child_u] if child & complete[child_u] else memo[child_u, child],
                        child, count) for child, count in groups.items())
        remaining, total, branches = units[i], 0, []
        for cost, child, count in costs:
            mass = min(remaining, count * caps[i])
            if mass:
                branches.append([str(child), count, mass])
                total += mass * cost
                remaining -= mass
                if child & complete[child_u]:
                    absorbing_edges += 1
                else:
                    pending.append((child_u, child))
            if not remaining:
                break
        require(remaining == 0 and total == val, 'policy row attains exact Bellman value')
        policy.append(dict(remaining=u, live=str(active), prime=primes[i],
                           numerator=str(val), mass_units=units[i], branches=branches))
        by_depth[7-u.bit_count()][str(primes[i])] += 1
    policy.sort(key=lambda r:(r['remaining'], int(r['live'])))
    terminals.sort(key=lambda r:int(r[0]))
    policy_out = dict(schema='adaptive-core7-positive-policy-v1',
                      scope='One attained head law: split each group mass over its matching actual leaves in increasing order up to their cap; finish absorbing histories with legal rows; terminal rows fill allowed residues first. Full tuples remain available for tail queries.',
                      epsilon_exact=str(epsilon), boundary_states=len(policy), terminal_states=len(terminals),
                      positive_group_edges=sum(len(r['branches']) for r in policy),
                      absorbing_edges=absorbing_edges,
                      selected_coordinate_counts_by_depth=[dict(c) for c in by_depth],
                      policy=policy, terminals=terminals,
                      input_sha256=sha256(raw).hexdigest(),
                      producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    policy_out=ctx.finish(policy_out)
    policy_bytes=(json.dumps(policy_out,indent=2)+'\n').encode()
    scores = []
    for rec in curve['records']:
        require(F(rec['epsilon_exact']) == fixed, 'same previously attained head baseline')
        best = rec['best']
        baseline = F(best['baseline_score_upper']) - fixed + epsilon
        extension = F(best['D7_score_upper']) - fixed + epsilon
        scores.append(dict(B=rec['B'], tau=best['tau'],
                           baseline_exact=str(baseline), baseline_decimal=float(baseline),
                           D7_exact=str(extension), D7_decimal=float(extension),
                           baseline_pass=baseline < 1, D7_pass=extension < 1))
    result.update(status='completed', epsilon_exact=str(epsilon), epsilon_decimal=float(epsilon),
                  survival_exact=str(1 - epsilon), fixed_order_exact=str(fixed),
                  improvement_exact=str(fixed - epsilon), improvement_decimal=float(fixed - epsilon),
                  root_prime=primes[choices[127, (1 << 154) - 1]], root_action_values=root_values,
                  raw_denominator=str(den[127]), table_sha256=table_digest.hexdigest(),
                  policy_sha256=sha256(policy_bytes).hexdigest(),
                  boundary_rows=len(policy), terminal_boundaries=len(terminals),
                  positive_edges=policy_out['positive_group_edges'], absorbing_edges=absorbing_edges,
                  curve_input_sha256=sha256(curve_raw).hexdigest(), stoploss_comparisons=scores)
    result.update(states=len(memo),stats=stats)
    require(result['status']=='completed','no result after resource limit')
    require(result['table_sha256']=='af038732667a6d1b89bb40bf244a26a09a918282fffce506fc018062bc81eab1','same complete value-table digest')
    return ctx.finish(result),policy_out


def write_policy(io,path,text):
    """Keep the full logical policy in bounded, recursively nested array parts."""
    import os
    from tempfile import TemporaryDirectory
    path=Path(path)
    value=json.loads(text,object_pairs_hook=io._unique)
    logical=io._bytes(value)
    require(logical.decode()==text,'canonical full policy bytes')
    directory=path.with_name(path.stem+'.parts')
    if directory.exists() or directory.is_symlink():
        io.read_artifact_bytes(path)
    with TemporaryDirectory(prefix='.'+path.stem+'-write-',dir=path.parent) as temporary:
        staging=Path(temporary)
        candidate=staging/path.name
        candidate_parts=staging/directory.name
        candidate_parts.mkdir()
        def save(item,route):
            encoded=io._bytes(item)
            kind='value'
            if len(encoded.splitlines())>io.PART_LINES:
                if isinstance(item,list):
                    require(len(item)>1,'split policy list has at least two elements')
                    middle=len(item)//2
                    chunks=[]
                    for start,stop in ((0,middle),(middle,len(item))):
                        part=save(item[start:stop],route+f'/{start:06d}-{stop:06d}')
                        chunks.append(dict(start=start,stop=stop,part=part))
                    encoded=io._bytes(dict(length=len(item),chunks=chunks))
                    kind='array'
                else:
                    require(isinstance(item,dict),'large policy node is an object or list')
                    encoded=io._bytes({key:({'kind':'inline','value':child}
                        if len(io._bytes(child).splitlines())<=40
                        else save(child,route+f'/{index:03d}'))
                        for index,(key,child) in enumerate(item.items())})
                    kind='object'
            require(len(encoded.splitlines())<=1000,'bounded semantic policy part')
            name=route+'.json'
            part=candidate_parts/name
            part.parent.mkdir(parents=True,exist_ok=True)
            part.write_bytes(encoded)
            return dict(path=name,sha256=sha256(encoded).hexdigest(),kind=kind)
        root=save(value,'content')
        manifest=dict(certificate_format=io.FORMAT,logical_sha256=sha256(logical).hexdigest(),
                      parts_directory=directory.name,root=root)
        candidate.write_bytes(io._bytes(manifest))
        require(io.read_artifact_bytes(candidate)==logical,'exact full hierarchical policy readback')
        previous_parts=staging/'previous.parts'
        saved_old_parts=installed_new_parts=False
        try:
            if directory.exists():
                os.replace(directory,previous_parts)
                saved_old_parts=True
            os.replace(candidate_parts,directory)
            installed_new_parts=True
            os.replace(candidate,path)
        except BaseException:
            if installed_new_parts:
                os.replace(directory,candidate_parts)
            if saved_old_parts:
                os.replace(previous_parts,directory)
            raise
    return len(text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    result,policy=calculate(args.base)
    io=_io.load_module('adaptive_core_output_io',args.base/'certificate_io.py')
    policy_path=args.base/'certificates/source_norms/source-budgets/adaptive_core7_policy.json'
    if args.write:
        write_policy(io,policy_path,json.dumps(policy,indent=2)+'\n')
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        require(policy==json.loads(io.read_artifact_bytes(policy_path),object_pairs_hook=io._unique),'exact complete positive-policy replay')
        require(result==json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=io._unique),'exact adaptive core replay')
    require(sha256(io.read_artifact_bytes(policy_path)).hexdigest()==result['policy_sha256'],'result binds complete logical policy')
    print(json.dumps({'schema':result['schema'],'mode':'write' if args.write else 'check','epsilon_exact':result['epsilon_exact'],'policy_rows':len(policy['policy'])}))

if __name__=='__main__':
    main()
