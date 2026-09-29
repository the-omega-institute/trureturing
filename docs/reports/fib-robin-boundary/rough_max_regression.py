#!/usr/bin/env python3
"""Known-value, small all-integer sigma-sieve and certificate corruption checks."""
import sys
sys.dont_write_bytecode = True

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from rough_max import build
from rough_max_check import check

KNOWN = [
    (7,1000,143,Fraction(168,143)),
    (7,4181,2431,Fraction(3024,2431)),
    (7,46188,26741,Fraction(33516,26741)),
    (7,10**6,508079,Fraction(35280,26741)),
    (7,10**12,388705330871,Fraction(30888345600,20458175309)),
    (1,5040,5040,Fraction(403,105)),
]


def expect_rejected(cert,label):
    try:
        check(cert)
    except (ValueError,KeyError):
        return label
    raise AssertionError(f'checker accepted corruption: {label}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True,help='results and certificate directory')
    OUT = ap.parse_args().out
    OUT.mkdir(parents=True,exist_ok=True)
    known_results = []
    certificates = []
    for y,bound,witness,value in KNOWN:
        cert = build(y,bound)
        certificates.append(cert)
        data = (json.dumps(cert,separators=(',',':'))+'\n').encode()
        path = OUT/f'certificate-y{y}-B{bound}.json'
        path.write_bytes(data)
        result = check(json.loads(path.read_bytes()))
        assert result['witness'] == witness,(y,bound,'unexpected witness',result)
        assert Fraction(*result['value']) == value,(y,bound,'unexpected exact value',result)
        result['certificate_path'] = path.name
        result['certificate_sha256'] = hashlib.sha256(data).hexdigest()
        known_results.append(result)

    # Every n up to 256 is evaluated using its actual integer divisor sum.
    # This includes noncanonical prime supports and exponent orders.
    cutoff = 256
    sigma = [0]*(cutoff+1)
    for d in range(1,cutoff+1):
        for n in range(d,cutoff+1,d):
            sigma[n] += d
    sieve_cases = 0
    for y in [1,2,7,13]:
        forbidden = [p for p in range(2,y+1)
                     if all(p%d for d in range(2,p))]
        best = Fraction(1)
        for bound in range(1,cutoff+1):
            if all(bound%p for p in forbidden):
                best = max(best,Fraction(sigma[bound],bound))
            result = check(build(y,bound))
            assert Fraction(*result['value']) == best,(y,bound,result,best)
            assert Fraction(sigma[result['witness']],result['witness']) == best
            sieve_cases += 1

    rejected = []
    cert = certificates[0]
    root_index = next(i for i,s in enumerate(cert['states']) if s['key'] == cert['root'])
    bad = copy.deepcopy(cert)
    bad['states'][root_index]['branches'].pop()
    rejected.append(expect_rejected(bad,'missing allowed branch'))
    bad = copy.deepcopy(cert)
    bad['states'][root_index]['value'] = [1,1]
    rejected.append(expect_rejected(bad,'false lower value'))
    bad = copy.deepcopy(cert)
    bad['states'][root_index]['value'] = [100,1]
    rejected.append(expect_rejected(bad,'unattained upper value'))
    bad = copy.deepcopy(cert)
    bad['states'][root_index]['witness'] = 1
    rejected.append(expect_rejected(bad,'incorrect attaining witness'))
    bad = copy.deepcopy(cert)
    bad['states'][root_index]['branches'][0]['child'][1] += 1
    rejected.append(expect_rejected(bad,'incorrect child budget'))
    bad = copy.deepcopy(cert)
    bad['primes'][0] = 13
    rejected.append(expect_rejected(bad,'skipped first allowed prime'))
    bad = copy.deepcopy(cert)
    bad['root'][2] += 1
    rejected.append(expect_rejected(bad,'incorrect root exponent cap'))
    bad = copy.deepcopy(cert)
    child_key = bad['states'][root_index]['branches'][0]['child']
    bad['states'] = [s for s in bad['states'] if s['key'] != child_key]
    rejected.append(expect_rejected(bad,'missing reachable child state'))

    result = {'status':'PASS','known_exact_results':known_results,
              'direct_sigma_sieve_cutoff':cutoff,
              'direct_sigma_sieve_thresholds':[1,2,7,13],
              'direct_sigma_sieve_comparisons':sieve_cases,
              'deliberate_corruptions_rejected':rejected,
              'source_hashes':{p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest()
                               for p in ['rough_max.py','rough_max_check.py','rough_max_regression.py']},
              'limitations':['Exact finite computation, not a Lean theorem.',
                             'The checker proves the supplied finite recurrence by exact arithmetic; the paper must justify canonical normalization to all rough integers.']}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
