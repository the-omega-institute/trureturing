"""Independent prime-power sieve check of Bradshaw Conjecture 20.

No code imported from the preregistration or another probe. D is computed
by its prime-factor formula, summing n/p once for each power p^k dividing n.
"""
from array import array
import json
import time


def C(a, b, n):
    return (a * n + b) // 2 if n % 2 else n // 2


def factor(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def D_trial(n):
    return sum(e * (n // p) for p, e in factor(n).items()) if n else 0


def derivative_sieve(limit):
    prime = bytearray(b'\x01') * (limit + 1)
    prime[:2] = b'\x00\x00'
    for p in range(2, __import__('math').isqrt(limit) + 1):
        if prime[p]:
            prime[p*p::p] = b'\x00' * ((limit - p*p) // p + 1)
    values = array('I', [0]) * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            power = p
            while power <= limit:
                for n in range(power, limit + 1, power):
                    values[n] += n // p
                power *= p
    return values


def main():
    start = time.monotonic()
    limit = 10**7
    pairs = [(5, 1), (5, 3), (7, 1), (7, 3), (7, 5)]
    expected = [[], [12419,20171,37727,134579,199259,301799,574319,
                    866891,1580291,1625411,8014031], [429], [],
                [29831,38051,76331,568031,888971,1855871,3095711]]
    top = max(C(a, b, limit-1) for a, b in pairs)
    values = derivative_sieve(top)
    assert all(values[n] == D_trial(n) for n in range(10000))
    anchors = []
    for (a, b), want in zip(pairs, expected):
        got = [n for n in range(1, limit+1)
               if values[C(a,b,n)] == C(a,b,values[n])]
        assert got == want, ((a,b), got, want)
        anchors.append({'a':a, 'b':b, 'solutions':got, 'matches_paper':True})
    a, b, n = 17, 7, 125
    witness = {'a':a, 'b':b, 'n':n, 'D_n':D_trial(n),
               'C_n':C(a,b,n), 'D_C_n':D_trial(C(a,b,n)),
               'C_D_n':C(a,b,D_trial(n)), 'D_75':D_trial(75),
               'factorization':factor(n),
               'squarefree':all(e == 1 for e in factor(n).values())}
    assert witness['D_C_n'] == witness['C_D_n'] == 641
    assert witness['squarefree'] is False
    result = {'method':'prime-power contribution sieve, trial-factor cross-check',
              'range':[1,limit], 'derivative_sieve_bound':top,
              'anchors':anchors, 'witness':witness,
              'wall_s':time.monotonic()-start}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
