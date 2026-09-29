#!/usr/bin/env python3
"""Finite reserve audit using only standard-library integer intervals.

No float is used in any mathematical comparison. Decimal is display-only.
This independent executable certificate is NOT a Lean/kernel proof.
"""
import argparse
from bisect import bisect_left, bisect_right
from decimal import Decimal, localcontext
import gzip
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys
import traceback

# Importing the shared engine must not create files beside the sources.
sys.dont_write_bytecode = True
ENGINE = Path(__file__).resolve().with_name('price_band.py')
spec = importlib.util.spec_from_file_location('prior_integer_interval_engine', ENGINE)
iv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(iv)  # Its main() is guarded; importing does not run it.
I, SCALE, ZERO, ONE = iv.I, iv.SCALE, iv.ZERO, iv.ONE
lograt, logiv, ceildiv = iv.lograt, iv.logiv, iv.ceildiv

LOW, HIGH = 144, 121393
GAMMA_M = 10000


def sqrt_integer(n):
    """Outward interval for sqrt(n); exact isqrt of n*SCALE**2."""
    assert n >= 0
    radicand = n * SCALE * SCALE
    q = isqrt(radicand)
    assert q*q <= radicand < (q+1)*(q+1)
    return I(q, q if q*q == radicand else q+1)


def gamma_interval(m):
    """H_m-log(m)-1/(2m) < gamma < H_m-log(m)-1/(2(m+1))."""
    h = I(sum(SCALE//j for j in range(1, m+1)),
          sum(ceildiv(SCALE, j) for j in range(1, m+1)))
    base = h-lograt(m)
    return I((base-I.rat(1, 2*m)).lo,
             (base-I.rat(1, 2*(m+1))).hi)


def exceeds_rational(lower, numerator, denominator):
    return lower * denominator > numerator * SCALE


def inclusive_sieve(n):
    """Independent inclusive sieve (different indexing from the imported engine)."""
    composite = bytearray(n+1)
    for p in range(2, isqrt(n)+1):
        if not composite[p]:
            for multiple in range(p*p, n+1, p):
                composite[multiple] = 1
    return [p for p in range(2, n+1) if not composite[p]]


def decimal_ratio(numerator, denominator):
    with localcontext() as ctx:
        ctx.prec = 28
        return str(Decimal(numerator) / denominator)


def run(out):
    out.mkdir(parents=True, exist_ok=True)
    primes = inclusive_sieve(HIGH)
    # Cross-check against the separately written exclusive sieve.
    assert primes == iv.prime_sieve(HIGH+1)
    gamma = gamma_interval(GAMMA_M)
    events = []
    logs = {}
    deficits = []
    prefix = [ZERO]
    for p in primes:
        lp = lograt(p)
        logs[p] = lp
        deficit = I.rat(1,p)-lograt(p+1,p)
        assert deficit.lo > 0, ('deficit sign unresolved',p,deficit.wire())
        deficits.append(deficit)
        prefix.append(prefix[-1]+deficit)
        power, k = p, 1
        while power <= HIGH:
            events.append((power,p,k))
            power *= p
            k += 1
    events.sort()
    values = [power for power,p,k in events]
    assert len(values) == len(set(values)), 'prime powers collided'
    cuts = sorted(set([LOW,HIGH]+[power for power in values if LOW < power < HIGH]))
    assert cuts[0] == LOW and cuts[-1] == HIGH
    assert all(a < b for a,b in zip(cuts,cuts[1:]))

    # Commit before cell arithmetic: both targets are fixed, no adaptive weakening.
    certificate = {
        'schema':'finite-prime-power-reserve-integer-interval-v1',
        'scale':str(SCALE), 'bits':iv.BITS, 'atanh_terms':iv.TERMS,
        'range':[LOW,HIGH], 'gamma_m':GAMMA_M, 'gamma':gamma.wire(),
        'targets':{'reserve_strict':[13,100000],
                   'claimed_minimum_strict':[1387077,10000000000],
                   'phi_barrier_nonnegative':[0,1]},
        'cell_convention':'[a,b), final cell [a,b]; Phi is continuous at prime-power events',
        'primes':[[p,logs[p].wire(),d.wire()] for p,d in zip(primes,deficits)],
        'events':[list(e) for e in events], 'cells':[], 'failures':[],
    }
    cells = certificate['cells']
    failures = certificate['failures']
    event_index = 0
    psi = ZERO
    p_sum = ZERO
    minimum_reserve = None
    minimum_barrier = None
    minimum_phi = None
    sampled_direct_sums = 0
    for cell_index,(a,b) in enumerate(zip(cuts,cuts[1:])):
        while event_index < len(events) and events[event_index][0] <= a:
            power,p,k = events[event_index]
            psi = psi+logs[p]
            p_sum = p_sum+I.rat(1,k*power)
            event_index += 1
        assert psi.lo > SCALE
        assert event_index == bisect_right(values,a)
        assert event_index == len(events) or events[event_index][0] >= b
        # For C=Psi(a), x -> log log x +(C-x)/(x log x)
        # has global minimum log log C at x=C, because its derivative
        # is (x-C)(log x+1)/(x^2 log^2 x), for x>1.
        phi_minimum = gamma+logiv(logiv(psi))-p_sum

        # p^2 >= 2b iff p >= ceil(sqrt(2b)); p <= a-1 exactly.
        root_floor = isqrt(2*b)
        root_ceil = root_floor if root_floor*root_floor == 2*b else root_floor+1
        left = bisect_left(primes,root_ceil)
        right = bisect_right(primes,a-1)
        assert left <= right
        if left:
            assert primes[left-1]*primes[left-1] < 2*b
        if left < len(primes):
            assert primes[left]*primes[left] >= 2*b
        assert right == 0 or primes[right-1] <= a-1
        assert right == len(primes) or primes[right] > a-1
        reserve = prefix[right]-prefix[left]
        total = phi_minimum+reserve
        # Since sqrt(x)*log(x) increases on x>1, using b gives a
        # lower bound on +1/(2*sqrt(x)*log(x)) throughout this cell.
        reciprocal_at_b = ONE/(sqrt_integer(b)*lograt(b)*2)
        barrier_gap = phi_minimum+reciprocal_at_b

        # Predetermined sparse audit of prefix subtraction against direct sums.
        if cell_index % 997 == 0 or cell_index == len(cuts)-2:
            direct = ZERO
            for j in range(left,right):
                direct = direct+deficits[j]
            assert reserve.lo <= direct.lo <= direct.hi <= reserve.hi
            sampled_direct_sums += 1

        row = {'index':cell_index,'a':a,'b':b,'events_consumed':event_index,
               'psi':psi.wire(),'P':p_sum.wire(),
               'phi_global_minimum':phi_minimum.wire(),
               'eligible_prime_indices':[left,right],
               'eligible_prime_count':right-left,
               'reserve':reserve.wire(),'total_lower_expression':total.wire(),
               'barrier_reciprocal_at_b':reciprocal_at_b.wire(),
               'barrier_gap_lower_expression':barrier_gap.wire()}
        cells.append(row)
        if not exceeds_rational(total.lo,13,100000):
            failures.append({'check':'reserve > 13/100000','cell':row})
        if not exceeds_rational(total.lo,1387077,10000000000):
            failures.append({'check':'reserve > 0.0001387077','cell':row})
        if barrier_gap.lo < 0:
            failures.append({'check':'Phi >= -1/(2 sqrt(x) log(x))','cell':row})
        if minimum_reserve is None or total.lo < minimum_reserve[0].lo:
            minimum_reserve = (total,row)
        if minimum_barrier is None or barrier_gap.lo < minimum_barrier[0].lo:
            minimum_barrier = (barrier_gap,row)
        if minimum_phi is None or phi_minimum.lo < minimum_phi[0].lo:
            minimum_phi = (phi_minimum,row)

    # No event at HIGH in this particular range. Assert instead of silently
    # dropping a possible final singleton or treating its changed P as fixed.
    assert HIGH not in values
    assert event_index == len(events)
    assert len(cells) == len(cuts)-1
    assert cells[0]['a'] == LOW and cells[-1]['b'] == HIGH
    assert all(x['b'] == y['a'] for x,y in zip(cells,cells[1:]))
    encoded = json.dumps(certificate,separators=(',',':')).encode()
    cert_path = out/'cells.json.gz'
    cert_path.write_bytes(gzip.compress(encoded,mtime=0))
    min_total,min_row = minimum_reserve
    min_barrier,barrier_row = minimum_barrier
    min_phi,phi_row = minimum_phi
    result = {
        'status':'PASS' if not failures else 'FAIL',
        'verification_kind':'standard-library integer-interval arithmetic; not Lean verified',
        'range':[LOW,HIGH], 'prime_count':len(primes),
        'prime_power_event_count':len(events),'cell_count':len(cells),
        'gamma_interval':gamma.decimal(), 'gamma_wire':gamma.wire(),
        'minimum_total_lower_expression_interval':min_total.decimal(),
        'minimum_total_lower_expression_wire':min_total.wire(),
        'minimum_total_cell':[min_row['a'],min_row['b']],
        'minimum_total_cell_index':min_row['index'],
        'minimum_total_phi_interval':I(*map(int,min_row['phi_global_minimum'])).decimal(),
        'minimum_total_reserve_interval':I(*map(int,min_row['reserve'])).decimal(),
        'minimum_barrier_gap_interval':min_barrier.decimal(),
        'minimum_barrier_gap_wire':min_barrier.wire(),
        'minimum_barrier_cell':[barrier_row['a'],barrier_row['b']],
        'minimum_phi_interval':min_phi.decimal(),
        'minimum_phi_cell':[phi_row['a'],phi_row['b']],
        'strict_target':'13/100000',
        'strict_claimed_minimum':'1387077/10000000000',
        'margin_above_target_lower':decimal_ratio(min_total.lo*100000-13*SCALE,SCALE*100000),
        'failure_count':len(failures),
        'direct_prefix_sum_audit_cells':sampled_direct_sums,
        'certificate_sha256':hashlib.sha256(encoded).hexdigest(),
        'compressed_certificate_sha256':hashlib.sha256(cert_path.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'script_path':Path(__file__).name,
        'imported_engine_path':ENGINE.name,
        'imported_engine_sha256':hashlib.sha256(ENGINE.read_bytes()).hexdigest(),
        'limitations':[
            'Log-series, gamma inequalities, calculus cell minimum, and the analytic Delta >= Phi+B bridge require mathematical justification outside this arithmetic executable.',
            'This arithmetic certificate is not a Lean theorem.',
            'Coverage is exactly x in [144,121393]; no statement outside this range is checked.'
        ],
    }
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    assert not failures, f'{len(failures)} failed comparisons; exact cells saved in {cert_path}'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True)
    args = ap.parse_args()
    try:
        run(args.out)
    except Exception as exc:
        args.out.mkdir(parents=True,exist_ok=True)
        (args.out/'exception.json').write_text(json.dumps({
            'status':'FAIL','exception':repr(exc),'traceback':traceback.format_exc()},indent=2)+'\n')
        raise


if __name__ == '__main__':
    main()
