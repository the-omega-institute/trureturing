"""Fixed full-private zero-set positivity test; no query or prime continuation."""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import argparse
import hashlib
import json


def head_rows(p, active):
    alive = [x for x in range(p*p)
             if x % p != p-1 and x != p-2
             and not (active and (x % p == 0 or x == 1))]
    return [F(sum(x % p == i for x in alive), p*p) for i in range(p)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--first-source', type=Path, required=True)
    parser.add_argument('--second-source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    checks = 0
    def ck(ok):
        nonlocal checks
        if not ok:
            raise ArithmeticError('fixed source or local-factor assumption failed')
        checks += 1
    rows = []
    for label, path in [('FC110', args.first_source), ('FC131', args.second_source)]:
        src = json.loads(path.read_text())
        private = tuple(src['private_primes'])
        ck(private == (11,13,17,19,23,29,31,37,41))
        for q in private:
            for p in (5,7):
                token = src['private_sources'][str(q)][str(p)]
                free = [F(x) for x in token['free']]
                selected = [[F(x) for x in token['selected_increment'][str(r)]]
                            for r in (1,2)]
                ck(len(free) == p and sum(x > 0 for x in free) == 1)
                ck(sum(x > 0 for seq in selected for x in seq) == 1)
        for r in (1,2):
            b5, b7 = head_rows(5, r == 1), head_rows(7, r == 2)
            a5, a7 = sum(b5), sum(b7)
            z5, z7 = a5-F(1,5), a7-F(1,7)
            zq = {q:1-(1+int(r == 2))*(F(1,q)+F(1,q*q))-F(1,q)
                  for q in private}
            K = prod(zq.values())
            table = {}
            max_deletions = {q:0 for q in private}
            for i in range(5):
                for j in range(7):
                    factors = []
                    for q in private:
                        token = src['private_sources'][str(q)]
                        count = (int(F(token['5']['free'][i]) > 0)
                                 + int(F(token['7']['free'][j]) > 0)
                                 + int(F(token['5']['selected_increment'][str(r)][i]) > 0)
                                 + int(F(token['7']['selected_increment'][str(r)][j]) > 0))
                        max_deletions[q] = max(max_deletions[q], count)
                        factor = 1-F(count,q)/zq[q]
                        ck(0 <= factor <= 1)
                        factors.append(factor)
                    table[i,j] = prod(factors)
            conditional = {j:sum(b5[i]*table[i,j] for i in range(5))
                           for j in range(7) if b7[j] > 0}
            mass = sum(b7[j]*conditional[j] for j in conditional)
            threshold = a5*a7-z5*z7
            margins = {j:v-F(1,5) for j,v in conditional.items()}
            total_margin = mass-threshold
            rows.append({'source':label,'root':r,
                         'head5_row_masses':[str(x) for x in b5],
                         'head7_row_masses':[str(x) for x in b7],
                         'max_active_roles':max_deletions,
                         'private_zero_product':str(K),
                         'conditional_head5_masses':{str(j):str(v) for j,v in conditional.items()},
                         'conditional_margins':{str(j):str(v) for j,v in margins.items()},
                         'normalized_joint_mass':str(mass),
                         'required_total_mass':str(threshold),
                         'total_margin':str(total_margin),
                         'conditional_pass':all(v >= 0 for v in margins.values()),
                         'total_pass':total_margin >= 0,
                         'minimum_row':min(margins,key=margins.get),
                         'minimum_conditional_margin':str(min(margins.values()))})
    result = {'scope':'fixed n2, all first-depth grouped roles, private axes then5 then7; no continuation',
              'source_hashes':{path.name:hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in (args.first_source,args.second_source)},
              'local_and_source_checks':checks,'cases':rows,
              'all_cases_pass':all(x['conditional_pass'] and x['total_pass'] for x in rows)}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks':checks,'all_cases_pass':result['all_cases_pass'],
                      'cases':[{'source':x['source'],'root':x['root'],
                                'conditional_pass':x['conditional_pass'],'total_pass':x['total_pass'],
                                'minimum_row':x['minimum_row'],
                                'minimum_conditional_margin':float(F(x['minimum_conditional_margin'])),
                                'total_margin':float(F(x['total_margin']))} for x in rows]}))


if __name__ == '__main__':
    main()
