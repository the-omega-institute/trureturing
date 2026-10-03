"""Exact certificates for common-centre cuts on arbitrary retained K8 tables.

Rebuilds the 824 C cap interface and integrates only the named centres with
832's local laws. Standard library only: no optimizer or 960-centre replay.
Inputs and output are explicit; normal operation compares a saved result.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from math import prod
from pathlib import Path
import argparse
import json
import sys

PINS = {
    'legacy_engine': 'c3bc91147205b8049581015a889af9a96236489789048ac6256aed355ef84c70',
    'centre_engine': 'a63339503f703fbd8e6f47148c12c0e5b9fafe475f88d5c6a891c1ea38e392f7',
    'candidate': '17557f86d60a40310275025219d893e28ba103b5f099cf53886a8eb8ef970aca',
    'result832': 'd3b417a48a822408223f614de0133f848fac4cc7663511aec3edb0961c15bf44',
}
CENTRES = ((3,0,1,1,1,1,1,1), (4,1,1,1,1,1,1,1), (2,0,1,1,1,1,1,1))
COUNTS = Counter()


def need(ok, label):
    COUNTS[label] += 1
    if not ok:
        raise ValueError(label)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def unique(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('duplicate JSON key: ' + key)
        out[key] = value
    return out


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def semantic_hash(value):
    return sha256((json.dumps(encode(value), sort_keys=True, separators=(',', ':'))+'\n').encode()).hexdigest()


def load_module(name, path):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def rational(value):
    need(type(value) is str, 'rational string')
    q = F(value)
    need(str(q) == value, 'canonical rational')
    return q


def sparse_vector(entries, length):
    out = [F(0)] * length
    seen = set()
    for i, value in entries:
        need(type(i) is int and 0 <= i < length and i not in seen, 'unique sparse index')
        seen.add(i)
        q = rational(value)
        need(q > 0, 'strictly positive retained sparse coefficient')
        out[i] = q
    return out


def sparse(terms):
    out = {}
    for i, value in terms:
        out[i] = out.get(i, F(0)) + value
    return [(i, value) for i, value in sorted(out.items()) if value]


def cell_law(engine, primes, leaves, probabilities, pattern, leaf_index, centre, low_limit):
    local = [engine.ternary_law(leaves[leaf_index], leaves[centre[0]], low_limit)]
    local += [engine.q_law(q, F(q-1, q-2), probabilities[j][pattern[j]],
                          centre[j+1], pattern[j], low_limit) for j, q in enumerate(primes)]
    atoms = [F(0)] * (low_limit+1)
    atoms[1] = F(1)
    for law in local:
        next_atoms = [F(0)] * (low_limit+1)
        for i in range(1, low_limit+1):
            if atoms[i]:
                for j in range(1, low_limit//i+1):
                    if law.atoms[j]:
                        next_atoms[i*j] += atoms[i]*law.atoms[j]
        atoms = next_atoms
    return engine.Law(prod((x.mass for x in local), start=F(1)),
                      prod((x.mean for x in local), start=F(1)), tuple(atoms))


def rebuild(legacy, engine, candidate, result832, low_limit=17):
    need(low_limit >= 17, 'h18 low-atom interface')
    old_names, _, old_rows, info = legacy.build(candidate, 31)
    need(len(old_names) == 1793 and len(old_rows) == 43446, 'inherited ABC dimensions')
    need(info['semantic_matrix_sha256'] == '01eda5c87b3a7d81ccc3bfb5c1e3a8cc14fc02af96f9c189c45d8a2950c21bd8', 'inherited 824 matrix identity')
    primes, leaves = tuple(candidate['primes']), tuple(candidate['leaves'])
    need(primes == (5,7,11,13,17,19,23) and leaves == (4,7,2,5,8), 'fixed source coordinates')
    need(candidate['phase45'] == 31 and [45,31] in candidate['actual_family'], 'same phase31')
    patterns = tuple(product(range(3), *(range(2) for _ in primes[1:])))
    probabilities = tuple(tuple(map(F, row)) for row in info['points'][2])
    expected_pi = ((F(4,15), F(4,15), F(7,15)),) + tuple((F(q-1,q*(q-2)), 1-F(q-1,q*(q-2))) for q in primes[1:])
    need(probabilities == expected_pi, 'specified infinite pure-comb C colour law')
    forbidden = set()
    for modulus, phase in candidate['actual_family']:
        if modulus in (3,9):
            continue
        rest, depth = modulus, 0
        while rest % 3 == 0:
            rest //= 3
            depth += 1
        axes = [j for j, q in enumerate(primes) if rest % q == 0]
        need(depth <= 2 and axes, 'K8 label structure')
        for sid, pattern in enumerate(patterns):
            if all(phase % primes[j] in candidate['partitions'][j][pattern[j]] for j in axes):
                for l, leaf in enumerate(leaves):
                    if leaf % (3**depth) == phase % (3**depth):
                        forbidden.add((l,sid))
    allowed = [(l,sid) for l in range(5) for sid in range(192) if (l,sid) not in forbidden]
    old_u = {tuple(name[1:]): i for i,name in enumerate(old_names) if name[0] == 'u'}
    need(len(forbidden) == 711 and len(allowed) == 249 and set(allowed) == set(old_u), 'all K8 zero and allowed cells')
    uid = {cell:i for i,cell in enumerate(allowed)}
    blocks = info['coefficient_blocks'][2]
    zkeys = [(int(b['D']),int(b['t']),int(b['h'])) for b in blocks]
    need(len(set(zkeys)) == len(zkeys) == 384 and all(t == 0 for _,t,_ in zkeys), 'all inherited C cap types')
    zid = {key:249+i for i,key in enumerate(zkeys)}
    remap = {old_u[cell]:uid[cell] for cell in allowed}
    remap.update({i:zid[tuple(name[2:])] for i,name in enumerate(old_names) if name[0] == 'z' and name[1] == 2})
    names = [['u',*cell] for cell in allowed] + [['z',*key] for key in zkeys] + [['epsilon']]
    cap_rows = []
    for label, terms, rhs in old_rows:
        if label[0:2] == ('epigraph',2) or list(label[0:2]) == ['epigraph',2]:
            need(rhs == 0 and all(i in remap for i,_ in terms), 'inherited literal C cap row')
            cap_rows.append({'label':list(label),'terms':sparse((remap[i],v) for i,v in terms),'rhs':'0'})
    need(len(cap_rows) == 9902, 'all inherited C cap rows')
    masses = [prod((probabilities[j][patterns[sid][j]] for j in range(7)), start=F(1)) for l,sid in allowed]
    need(min(masses) > 0, 'all cell masses positive')
    losses = {zid[key]:F(block['loss']) for key,block in zip(zkeys,blocks)}
    need(min(losses.values()) >= 0, 'all head losses nonnegative')
    centre_laws = {}
    hinges = {}
    rows = list(cap_rows)
    for centre in CENTRES:
        laws = [cell_law(engine,primes,leaves,probabilities,patterns[sid],l,centre,low_limit) for l,sid in allowed]
        for i,law in enumerate(laws):
            need(law.mass == masses[i] and sum(law.atoms) <= law.mass, 'complete cell mass')
            need(sum(n*law.atoms[n] for n in range(len(law.atoms))) <= law.mean, 'complete mean dominates low atoms')
        b = [engine.hinge(law,18) for law in laws]
        need(min(b) >= 0, 'actual centre cell hinge nonnegative')
        terms = [(i,b[i]-10*masses[i]) for i in range(249)]
        terms += [(i,10*loss) for i,loss in losses.items()] + [(633,F(1))]
        rows.append({'label':['centre_gate',*centre],'terms':sparse(terms),'rhs':'0'})
        centre_laws[centre], hinges[centre] = laws, b
    matrix = {'centres':CENTRES,'variables':names,'inequalities':rows,
              'equality':{'label':'mass1','terms':list(enumerate(masses)),'rhs':'1'}}
    old_table = {(r['leaf_index'],r['pattern_id']):F(r['u']) for r in candidate['nonzero_u']}
    old_u_values = [old_table.get(cell,F(0)) for cell in allowed]
    old_state = canonical_state(old_u_values,cap_rows,hinges,losses,masses)
    need(old_state['mass'] == F(result832['inherited_exact']['M']), '832 inherited raw mass')
    need(old_state['L'] == F(result832['inherited_exact']['L']), '832 inherited head lower bound')
    for witness in result832['envelope_witnesses']:
        centre = tuple(witness['centre_index'])
        need(centre in CENTRES[:2], '832 selected witness binding')
        value = sum((law.mean*u for law,u in zip(centre_laws[centre],old_u_values)), F(0))
        need(value == F(witness['complete_mean']), '832 complete witness mean')
    single = result832['single_centre_obstruction']
    c = tuple(single['centre'])
    need(c == CENTRES[0], '832 h18 one-centre identity')
    need(old_state['hinges'][0] == F(single['integer_hinges_0_to28'][18]), '832 actual h18 hinge')
    return {'matrix':matrix,'semantic_matrix_sha256':semantic_hash(matrix),'allowed':allowed,
            'masses':masses,'cap_rows':cap_rows,'losses':losses,'centre_laws':centre_laws,
            'hinges':hinges,'controls832':{'M':old_state['mass'],'L':old_state['L'],
            'A_hinge18':old_state['hinges'][0],'named_complete_means_checked':2}}


def canonical_state(u, cap_rows, hinges, losses, masses):
    x = list(u) + [F(0)]*385
    for row in cap_rows:
        z = [(i,a) for i,a in row['terms'] if i >= 249]
        need(len(z) == 1 and 249 <= z[0][0] < 633 and z[0][1] == -1, 'literal cap epigraph')
        value = sum((a*u[i] for i,a in row['terms'] if i < 249),F(0))
        x[z[0][0]] = max(x[z[0][0]],value)
    mass = sum((m*v for m,v in zip(masses,u)),F(0))
    L = mass-sum((a*x[i] for i,a in losses.items()),F(0))
    H = [sum((a*v for a,v in zip(hinges[c],u)),F(0)) for c in CENTRES]
    return {'x':x,'mass':mass,'L':L,'hinges':H,'gates':[10*L-h for h in H]}


def verify(cert, built):
    need(cert['schema'] == 'e7-arbitrary-retained-common-centre-certificate-v1', 'certificate schema')
    need(cert['source_pins'] == PINS, 'certificate exact source inputs')
    need(cert['threshold'] == 18 and cert['tail_coefficient'] == '0', 'fixed h18 zero tail')
    need(cert['centres'] == encode(CENTRES), 'certificate actual centres')
    need(cert['semantic_matrix_sha256'] == built['semantic_matrix_sha256'], 'complete rebuilt matrix semantic identity')
    rows = built['matrix']['inequalities']
    need(len(rows) == 9905 and len(built['matrix']['variables']) == 634, 'master dimensions')
    # A concrete table separates the A/B necessary master from the C cut.
    primal = cert['AB_feasible_table']
    u = sparse_vector(primal['u'],249)
    state = canonical_state(u,built['cap_rows'],built['hinges'],built['losses'],built['masses'])
    need(state['mass'] == 1, 'AB table exact M1')
    epsilon = rational(primal['epsilon'])
    need(epsilon == min(state['gates'][:2]) and F(3,5000) < epsilon < F(7,10000), 'AB strict positive margin')
    need(state['gates'][2] < -F(1,10), 'C strictly excludes the AB table')
    state['x'][633] = epsilon
    for row in rows[:9904]:
        need(sum((a*state['x'][i] for i,a in row['terms']),F(0)) <= 0, 'AB every original row')
    leafmax = [max((u[i] for i,(j,_) in enumerate(built['allowed']) if j == l),default=F(0)) for l in range(5)]
    scale = sum(leafmax)
    need(scale > 0 and sum(v/scale for v in leafmax) == 1, 'legal leaf-envelope rescaling')
    need(all(u[i]/scale <= leafmax[l]/scale for i,(l,_) in enumerate(built['allowed'])), 'all legal retained cell envelopes')
    # A rational dual applies to every nonnegative table, without upper boxes.
    dual = cert['ABC_upper_certificate']
    y = sparse_vector(dual['inequality_multipliers'],len(rows))
    lam = rational(dual['mass_multiplier'])
    beta = y[9902:]
    need(beta == [F(1,2),F(0),F(1,2)], 'one fixed A/C half mixture')
    need(sum(beta) == 1, 'free epsilon gate coefficient')
    column = [F(0)]*634
    cap_cost = {i:F(0) for i in range(249,633)}
    for k,(weight,row) in enumerate(zip(y,rows)):
        if weight:
            for i,a in row['terms']:
                column[i] += weight*a
            if k < 9902:
                zi = next(i for i,_ in row['terms'] if i >= 249)
                cap_cost[zi] += weight
    for zi,cost in cap_cost.items():
        need(cost <= 10*built['losses'][zi], 'all cap block budgets')
    for i,mass in enumerate(built['masses']):
        column[i] += lam*mass
    need(column[633] == 1, 'dual free epsilon exact identity')
    for value in column[:633]:
        need(value >= 0, 'all unbounded nonnegative columns')
    need(-F(44,1000) < lam < -F(43,1000) < -F(1,25), 'exact strict negative upper bound')
    return {'schema':'e7-arbitrary-retained-common-centre-result-v1','status':'pass',
            'evidence':'ordinary proof and exact rational certificate; no Lean claim',
            'source_pins':PINS,'semantic_matrix_sha256':built['semantic_matrix_sha256'],
            'scope':'same infinite pure-comb C/phase31/K8 first-colour tables/inherited head/raw hinge at h18; zero tail',
            'dimensions':{'u':249,'forced_zero_cells':711,'cap_blocks':384,'cap_rows':9902,'gate_rows':3,'variables':634,'rows':9905},
            'controls832':built['controls832'],
            'AB_counterexample':{'positive_u_entries':sum(v>0 for v in u),'M':state['mass'],'L':state['L'],
              'actual_hinges18':state['hinges'],'gate_values':state['gates'],'epsilon':epsilon,
              'legal_rescale_factor':scale,'legal_leaf_weights':[v/scale for v in leafmax],
              'rows_checked':9904,'interpretation':'A/B feasibility is insufficient; one common C centre excludes this same table'},
            'all_table_dual':{'mass_multiplier':lam,'gate_weights':beta,
              'positive_cap_multipliers':sum(v>0 for v in y[:9902]),'positive_gate_multipliers':sum(v>0 for v in beta),
              'cap_budgets_checked':384,'u_columns_checked':249,'all_nonnegative_columns_checked':633,
              'minimum_column_slack':min(column[:633]),'rational_margin':'1/25',
              'statement':'(H_A(18)+H_C(18))/2 >= 10 L(u)+(1/25)M(u) for every u>=0 on the allowed K8 cells',
              'consequence':'no nonzero table in this fixed interface can make the raw all-layout hinge criterion positive at h18, even with zero tail'},
            'boundaries':['no other source, selected head, phase, or actual-survivor normalization is excluded',
                          'no other threshold is settled by this h18 certificate',
                          'no finite original covering family or Erdos7 resolution is claimed'],
            'optimizer_called':False,'full_960_centre_tensor_called':False}


def main():
    parser = argparse.ArgumentParser()
    for name in ('legacy-engine','centre-engine','candidate','result832','certificate','result'):
        parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--write-result',action='store_true')
    args = parser.parse_args()
    paths = {name:getattr(args,name) for name in PINS}
    for name,path in paths.items():
        need(digest(path) == PINS[name], 'immutable input '+name)
    legacy = load_module('e7_arbitrary_profile_legacy',args.legacy_engine)
    engine = load_module('e7_arbitrary_profile_centres',args.centre_engine)
    built = rebuild(legacy,engine,read_json(args.candidate),read_json(args.result832))
    result = verify(read_json(args.certificate),built)
    result['certificate_sha256'] = digest(args.certificate)
    result['consumer_sha256'] = digest(Path(__file__))
    result = encode(result)
    if args.write_result:
        args.result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        need(read_json(args.result) == result, 'complete deterministic result comparison')
    print(json.dumps({'status':'pass','semantic_matrix_sha256':built['semantic_matrix_sha256'],
          'all_table_dual':result['all_table_dual'],'checks':sum(COUNTS.values()),
          'action':'written' if args.write_result else 'compared'},indent=2))


if __name__ == '__main__':
    main()
