#!/usr/bin/env python3
"""Exact independent audit of the fixed109-source joint q7/q11 retention dual.

Only stdlib is used. Source atoms are reconstructed from literal original
congruences. Each required query vector is obtained in two ways: categorical
closed formulas and explicit local residue enumeration with a truncated
root1-count polynomial. No discovery code is read or imported.
"""
import argparse
from fractions import Fraction as F
import hashlib
import itertools
import json
from math import gcd, lcm, prod
from pathlib import Path

PINS = {
 'clustered_global_phase_fixture.json': '4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
 'clustered_higher_pure_capacity_obstruction.json': 'ae2f90ae8f3c109cf4354dbe74377f0b1597a6b81901e85c8419934504b9530e',
 'remaining33_global_root_exclusion_certificate.json': 'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4',
}
WITNESS_SHA = '1511cbb74aedd06b8e6750ebf5dfde886ee653bb545df029cd93d7535baa98cf'
DIAGNOSTIC_SHA = 'fa01b794feb608958ab99ff8ac3a21d01bff32b80693592dd01b0d99ad0e29eb'
EXPECTED = F('1507661452610803341661/8686831052451071520000000000000')
Q = (7, 11, 13, 17, 19)
I = (0, 1, 2, 4, 5)
J = tuple(v for v in range(20) if v != 5)
LIVE = [(l,m) for l in I for m in J if not (l < 3 and m < 5)]
G = F(200163067, 201247200)
COUNTS = {}


def check(ok, label):
    COUNTS[label] = COUNTS.get(label, 0) + 1
    if not ok:
        raise RuntimeError('independent audit failed: ' + label)


def digest(obj):
    return hashlib.sha256(json.dumps(obj, separators=(',', ':'), sort_keys=True).encode()).hexdigest()


def split_original(item):
    central = item['modulus']
    outer = {}
    for p in Q:
        power = 1
        while central % p == 0:
            central //= p
            power *= p
        if power != 1:
            outer[p] = power
    return central, outer


def category7(x):
    return (0 if x == 1 else 1) if x % 7 == 1 else x % 7


def central_weight(l, m):
    return F(1 if l == 4 else 2, 9) * F(3 if m == 10 else 4, 75)


def selector(kind, address, leaf, p):
    mass = F(1 if leaf == 4 else 2, 9) if p == 3 else F(3 if leaf == 10 else 4, 75)
    if kind == 0:
        return mass
    if kind == 1:
        return mass if leaf // p == address else F(0)
    if kind == 2:
        return mass if leaf == address else F(0)
    if leaf != address:
        return F(0)
    if p == 3:
        return F(81, 82) if leaf == 4 else F(1)
    return F(4, 5) * (F(1875, 1876) if leaf == 10 else F(1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--witness', type=Path, default=None)
    parser.add_argument('--output', type=Path, default=None)
    parser.add_argument('--diagnostic', type=Path, default=None)
    args = parser.parse_args()
    data = {}
    for name, sha in PINS.items():
        raw = (args.directory / name).read_bytes()
        check(hashlib.sha256(raw).hexdigest() == sha, 'canonical input pin')
        data[name] = json.loads(raw)
    witness_path = args.witness or args.directory / 'clustered_q7_q11_retention_obstruction.json'
    raw = witness_path.read_bytes()
    check(hashlib.sha256(raw).hexdigest() == WITNESS_SHA, 'portable witness pin')
    candidate = json.loads(raw)
    check(candidate['source_sha256'] == PINS, 'numeric witness provenance')
    row_keys = ('mode','support','query7','query11','left','right','numerator')
    candidate['dual_rows'] = [dict(zip(row_keys,row)) for row in candidate['dual_rows']]
    diagnostic = None
    if args.diagnostic is not None:
        diag_raw = args.diagnostic.read_bytes()
        check(hashlib.sha256(diag_raw).hexdigest() == DIAGNOSTIC_SHA, 'discovery numeric JSON pin')
        diagnostic = json.loads(diag_raw)
        check(diagnostic['input_sha256'] == PINS, 'discovery input identity')
        check(diagnostic['dual_rows'] == candidate['dual_rows'], 'all2568 portable rows match discovery JSON')
    base = data['clustered_global_phase_fixture.json']['actual_originals']
    previous = data['clustered_higher_pure_capacity_obstruction.json']
    added = []
    gamma = []
    for p, weak, density in ((3, 4, F(2)), (5, 2, F(4, 3))):
        this_prime = []
        for h in range(3, 7):
            item = {'modulus': p**h, 'residue': weak + p*p*sum(p**k for k in range(h-3))}
            added.append(item)
            this_prime.append(item)
        for a, b in itertools.combinations(this_prime, 2):
            check(a['residue'] != b['residue'] % a['modulus'], 'actual pure cylinders disjoint')
        capacity = F(1, p*p) - sum((F(1, t['modulus']) for t in this_prime), F(0))
        gamma.append(F(1, p*p) / (density * capacity))
        for item in this_prime:
            check((weak + 2*p*p) % (p**3) != item['residue'] % (p**3), 'entire nested query child survives')
    check(gamma == [F(81,82), F(1875,1876)], 'actual central deep capacities')
    check(added == [{k:t[k] for k in ('modulus','residue')}
                    for t in previous['first_tested_success']['added_higher_pure_originals']], 'same681 eight pure originals')
    family = base + added
    check(len(base) == 101 and len(family) == 109, 'actual109 family size')
    check(len({t['modulus'] for t in family}) == 109, 'distinct numerical moduli')
    for item in family:
        check(item['modulus'] > 1 and item['modulus'] % 2 == 1 and 0 <= item['residue'] < item['modulus'], 'legal odd original')
        check(432297622003171927 % item['modulus'] != item['residue'], 'one integer avoids all109 originals')
    check(lcm(*(t['modulus'] for t in family)) == 1190750449028765625, 'actual common period')
    # Rebuild the literal reduction: all mixed pair events lie inside root1
    # at both endpoints, and an unguarded qs original realizes every pair.
    roots_pairs = set()
    unary = {p:[] for p in Q}
    central_originals = []
    for item in base:
        cm, outer = split_original(item)
        check(225 % cm == 0, 'all original central predicates resolve at225')
        check(len(outer) <= 2, 'no omitted higher outside interaction')
        if not outer:
            central_originals.append(item)
        elif len(outer) == 1:
            p, power = next(iter(outer.items()))
            check(power in (p, p*p), 'unary exponent at most2')
            if power == p*p:
                check(item['residue'] % (p*p) == 1, 'only special square child deleted')
            unary[p].append((cm, power, item['residue']))
        else:
            for p in outer:
                check(item['residue'] % p == 1, 'pair original implies both roots1')
            if cm == 1 and all(power == p for p,power in outer.items()):
                roots_pairs.add(tuple(sorted(outer)))
    check(roots_pairs == set(itertools.combinations(Q,2)), 'all ten unguarded root pairs present')
    coarse_data = []
    for l,m in LIVE:
        r9, r25 = l//3 + 3*(l%3), m//5 + 5*(m%5)
        central = r9 + 9*((r25-r9)*14 % 25)
        check(all(central % t['modulus'] != t['residue'] for t in central_originals), 'actual central survivor cell')
        atoms = {}
        for p in Q:
            atoms[p] = tuple(x for x in range(p*p) if x % p != 0 and
                             all(central % cm != residue % cm or x % power != residue % power
                                 for cm,power,residue in unary[p]))
            for x in atoms[p]:
                check(x % p != 0, 'outside pure root0 excluded')
            if p != 7:
                check(all(9 + p*j in atoms[p] for j in range(p)), 'root9 entirely undeleted')
        categories = [tuple(x for x in atoms[7] if category7(x) == k) for k in range(7)]
        check(sorted(x for xs in categories for x in xs) == list(atoms[7]), 'seven categories partition actual q7 atoms')
        check(len(categories[0]) in (0,1) and len(categories[1]) in (0,6), 'root1 categories are exact whole blocks')
        for k in range(2,7):
            check(len(categories[k]) in (0,7), 'non1 root category is whole root')
        A = {p:F(sum(x % p == 1 for x in atoms[p]),p*(p-1)) for p in Q[1:]}
        B = {p:F(sum(x % p != 1 for x in atoms[p]),p*(p-1)) for p in Q[1:]}
        coarse_data.append({'cell':(l,m), 'central':central, 'atoms':atoms, 'categories':categories, 'A':A, 'B':B})

    # The formulas and literal finite residue queries are rebuilt separately.
    # No source factorization is imposed on theta: each joint category has
    # its own independent variable, including all7/11 correlations.
    for c in coarse_data:
        cats7 = c['categories']
        def cat11(x):
            root = x % 11
            if root == 1:
                return 0 if x == 1 else 1
            return root if root < 9 else 9
        cats11 = [tuple(x for x in c['atoms'][11] if cat11(x) == k) for k in range(10)]
        check(sorted(x for xs in cats11 for x in xs) == list(c['atoms'][11]), 'ten categories partition actual11 atoms')
        check(len(cats11[0]) in (0,1) and len(cats11[1]) in (0,10), 'exact11 root1 blocks')
        check(len(cats11[9]) == 22, 'free11 category contains both entire roots9and10')
        for k in range(2,9):
            check(len(cats11[k]) in (0,11), 'exact11 non1 root category')
        c['literal7'], c['formula7'] = {}, {}
        c['literal11'], c['formula11'] = {}, {}
        for p,cats,query_list in ((7,cats7,range(-1,8)), (11,cats11,range(-1,10))):
            literal, formula = {}, {}
            for query in query_list:
                lit, form = [], []
                for k,xs in enumerate(cats):
                    mass = F(len(xs),p*(p-1))
                    if query == -1:
                        chosen, cap_inverse, closed = xs, 1, mass
                    elif (p == 7 and query < 6) or (p == 11 and query < 9):
                        root = query+1
                        chosen = [x for x in xs if x % p == root]
                        cap_inverse = p-1
                        if p == 11 and k == 9 and root == 9:
                            closed = F(1)
                        else:
                            closed = (p-1)*mass if (k < 2 and root == 1) or (k >= 2 and k == root) else F(0)
                    else:
                        #7 indices6/7 are lift0/other;11 index9 is lift0.
                        cat = query-6 if p == 7 else 0
                        selected_atom = 1 if cat == 0 else 1+p
                        chosen = [x for x in xs if x == selected_atom]
                        cap_inverse = p*(p-2)
                        closed = F(p-2,p-1) if k == cat and xs else F(0)
                    value = F(len(chosen)*cap_inverse,p*(p-1))
                    check(value == closed, 'literal unary query equals category formula')
                    check(not xs or mass > 0, 'live category positive unary mass')
                    check(bool(xs) or value == 0, 'dead unary category has zero query mass')
                    lit.append(value)
                    form.append(closed)
                literal[query],formula[query] = lit,form
            c['literal'+str(p)],c['formula'+str(p)] = literal,formula
        check(F(10,11) >= F(9,10), 'deepother11 dominated by firstroot1')
        check(F(6,7) >= F(5,6), 'deepother7 dominated by firstroot1')
        # On the representativefree11 category, fixedroot9 queries receive1,
        # whereas unqueried mass is2/10; these must not be identified.
        check(c['literal11'][-1][9] == F(1,5), 'free11 integrated mass2over10')
        check(c['literal11'][8][9] == 1, 'free11 literalroot9 normalized mass1')
        for k,xs in enumerate(cats11):
            mass10 = F(sum(x % 11 == 10 for x in xs)*10,110)
            check(mass10 == c['literal11'][8][k], 'globalfree root9and10 same category response')
        c['remaining_literal'],c['remaining_formula'] = {},{}
        for mask in range(8):
            #Literal polynomial tracks the numberof distinguished root1s.
            poly0,poly1 = F(1),F(0)
            for i,p in enumerate(Q[2:]):
                queried = bool(mask & (1<<i))
                chosen = [x for x in c['atoms'][p] if not queried or x % p == 9]
                cap_inverse = p-1 if queried else 1
                z0 = F(sum(x % p != 1 for x in chosen)*cap_inverse,p*(p-1))
                z1 = F(sum(x % p == 1 for x in chosen)*cap_inverse,p*(p-1))
                poly0,poly1 = poly0*z0,poly1*z0+poly0*z1
            free = [p for i,p in enumerate(Q[2:]) if not mask & (1<<i)]
            b = prod((c['B'][p] for p in free),start=F(1))
            ff = b + sum((c['A'][p]*prod((c['B'][q] for q in free if q != p),start=F(1)) for p in free),F(0))
            check(poly0 == b and poly0+poly1 == ff, 'literal other-coordinate convolution agrees')
            check(b > 0, 'other-coordinate no-root1 factor positive')
            c['remaining_literal'][mask] = (poly0+poly1,poly0,F(0))
            c['remaining_formula'][mask] = (ff,b,F(0))

    response_cache = {}
    def response(ci,support,query7,query11):
        key=(ci,support,query7,query11)
        if key not in response_cache:
            check(0 <= support < 32, 'global joint support address')
            check(query7 in range(8) if support & 1 else query7 == -1, 'global7 query address')
            check(query11 in range(10) if support & 2 else query11 == -1, 'global11 query address')
            c=coarse_data[ci]
            rows=[]
            for k in range(7):
                values=[]
                for h in range(10):
                    root1_count=int(k < 2)+int(h < 2)
                    lit=c['literal7'][query7][k]*c['literal11'][query11][h]*c['remaining_literal'][support>>2][root1_count]
                    form=c['formula7'][query7][k]*c['formula11'][query11][h]*c['remaining_formula'][support>>2][root1_count]
                    check(lit == form, 'joint literal query vector equals categorical formula')
                    if root1_count == 2:
                        check(lit == 0, 'actual7times11 pair excludes both roots1')
                    values.append(lit)
                rows.append(values)
            response_cache[key]=rows
        return response_cache[key]

    active=[]
    by_cell=[[] for _ in LIVE]
    source_all=[]
    for ci,c in enumerate(coarse_data):
        rs=response(ci,0,-1,-1)
        for k in range(7):
            for h in range(10):
                value=G*central_weight(*LIVE[ci])*rs[k][h]
                source_all.append(value)
                if value:
                    by_cell[ci].append((len(active),k,h))
                    active.append((ci,k,h,value))
                else:
                    #Positive remainingB means a dead column has either a
                    #dead unary category or both root1 flags; every query
                    #then remainszero under the explicit formulas above.
                    check(c['literal7'][-1][k] == 0 or c['literal11'][-1][h] == 0 or (k<2 and h<2), 'all omitted columns structurally query-null')
    check(len(active) == 3484 and len(source_all) == 5600, 'all joint field dimensions')
    total_source=sum((value/G for _,_,_,value in active),F(0))
    check(total_source == F('305684996597/646498195200'), 'same actual common-source mass')
    if diagnostic is not None:
        variables=[{'cell':list(LIVE[ci]),'category7':k,'category11':h,'theta':'0'} for ci,k,h,_ in active]
        check(diagnostic['variables'] == variables, 'all3484 diagnostic variable identities')
        check(diagnostic['source_coefficient'] == [str(v) for _,_,_,v in active], 'all3484 source coefficients agree')
    coefficients=list(map(F,data['remaining33_global_root_exclusion_certificate.json']['combined512_coefficients']))
    check(len(coefficients) == 512, 'complete512 fee groups')
    for bit,p in enumerate(Q[1:],1):
        coefficients[32*8+(1<<bit)] += G/F(p*(p-2))
    denominator=candidate['dual_denominator']
    check(denominator == 10**12, 'literal dual denominator')
    check(len(candidate['dual_rows']) == 2568, 'literal2568 dual rows')
    budgets=[F(0) for _ in range(512)]
    debit=[F(0) for _ in active]
    vector_records=[]
    addresses=set()
    for row in candidate['dual_rows']:
        mode,support,q7,q11,left,right,numerator=(row[k] for k in row_keys)
        address=(mode,support,q7,q11,left,right)
        check(address not in addresses, 'unique global literal dual query')
        addresses.add(address)
        check(0<=mode<16 and 0<=support<32, 'legal complete fee address')
        ex,ey=divmod(mode,4)
        check(left in ((0,),(0,1),I,I)[ex], 'legal ternary selector')
        check(right in ((0,),(0,1,2,3),J,J)[ey], 'legal quinary selector')
        check(type(numerator) is int and numerator>=0, 'nonnegative literal dual multiplier')
        multiplier=F(numerator,denominator)
        budgets[32*mode+support] += multiplier
        sparse=[]
        for ci,(l,m) in enumerate(LIVE):
            central=selector(ex,left,l,3)*selector(ey,right,m,5)
            if central == 0:
                continue
            table=response(ci,support,q7,q11)
            for vi,k,h in by_cell[ci]:
                value=central*table[k][h]
                check(value>=0, 'nonnegative literal joint vector entry')
                if value:
                    sparse.append([vi,str(value)])
                    debit[vi] += multiplier*value
        vector_records.append({'query':list(address),'nonzero_entries':len(sparse),'sparse_vector_sha256':digest(sparse)})
    for spent,limit in zip(budgets,coefficients):
        check(0<=spent<=limit, 'each512 exact full-fee dual budget')
    residuals=[value-cost for (_,_,_,value),cost in zip(active,debit)]
    upper=sum((max(F(0),r) for r in residuals),F(0))
    check(upper == EXPECTED, 'independent exact joint upper')
    check(str(upper) == candidate['expected']['universal_upper'], 'portable expected upper agreement')
    check(upper < F(1,10**9) < F(193,100000), 'joint strict threshold obstruction')
    if diagnostic is not None:
        check(str(upper) == diagnostic['exact_universal_upper'], 'diagnostic exact upper agreement')
    R=F(82,81)*F(1876,1875)
    lifted=R*upper
    check(lifted == F('1507661452610803341661/8576320051036237500000000000000'), 'exact central density lifting arithmetic')
    check(lifted < F(193,100000), 'lifted bound below target')
    result={
      'schema':'clustered-q7-q11-retention-independent-v1','status':'PASS',
      'new_lean_verification':False,'optimizer_used':False,
      'input_sha256':PINS,'witness_sha256':WITNESS_SHA,
      'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'method':'Original109 congruences; literal q-squared atom reconstruction; independent root1-count convolution and categorical query formulas; full512 fees and literal rational dual.',
      'active_field_columns':len(active),'potential_field_columns':len(source_all),
      'source_mass':str(total_source),'dual_denominator':denominator,'dual_term_count':len(vector_records),
      'fee_coefficients':[str(x) for x in coefficients],'dual_group_spending':[str(x) for x in budgets],
      'source_coefficient':[str(v) for _,_,_,v in active],
      'query_vectors':vector_records,'query_vectors_sha256':digest(vector_records),
      'residuals':[{'cell':list(LIVE[ci]),'category7':k,'category11':h,'value':str(r)} for (ci,k,h,_),r in zip(active,residuals)],
      'exact_universal_upper':str(upper),'exact_universal_upper_decimal':float(upper),
      'central_density_domination_factor':str(R),'lifted_upper':str(lifted),'lifted_upper_decimal':float(lifted),
      'target':'193/100000','checks':COUNTS,'check_count':sum(COUNTS.values()),
      'scope':'Fixed109 phase/source family, n4 central caps, arbitrary[0,1]joint central-coarse+q7seven+q11ten-category fields. Each query fixes both outside choices globally; all512 full fees. Separate ordinary measurable-coarsening and joint-central-density-domination proofs extend this upper to measurable central7/11 fields and nu<=8/3 ambient Haar on the same pure survivors, keeping the outside kernel and fees fixed. Does not bound fields depending on13/17/19, changed outside kernels, marginal-only central caps, or revised height-specific fees. Does not prove exact zero optimum or an arithmetic covering.'
    }
    output=args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'status':'PASS','check_count':result['check_count'],'active_columns':len(active),
                      'dual_terms':len(vector_records),'upper':str(upper),'upper_decimal':float(upper),
                      'lifted_upper':str(lifted),'output':str(output)},indent=2))


if __name__ == '__main__':
    main()
