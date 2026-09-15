"""Check the complete integer certificate for Goel's multiplier range through 200.

Run with Python 3.10+ beside certificate.json. Only the standard library is used.
The decoded input is mathematical data, never executed. The proof reducing all
prime q to this finite certificate is in the accompanying theory appendix.
This is an integer certificate check, not Lean kernel certification.
"""
from __future__ import annotations

import base64
import hashlib
import json
import zlib
from functools import lru_cache
from math import gcd, prod
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def fib_pair(n: int, modulus: int) -> tuple[int, int]:
    require(n >= 0 and modulus >= 2, "invalid Fibonacci arguments")
    a, b = 0, 1
    for bit in bin(n)[2:]:
        c = a * (2 * b - a) % modulus
        d = (a * a + b * b) % modulus
        a, b = (d, (c + d) % modulus) if bit == "1" else (c, d)
    return a, b


def matrix_mul(a: tuple[int, ...], b: tuple[int, ...], m: int) -> tuple[int, ...]:
    return ((a[0]*b[0]+a[1]*b[2]) % m, (a[0]*b[1]+a[1]*b[3]) % m,
            (a[2]*b[0]+a[3]*b[2]) % m, (a[2]*b[1]+a[3]*b[3]) % m)


def q_power(n: int, m: int) -> tuple[int, ...]:
    require(n >= 0 and m >= 2, "invalid matrix arguments")
    result, base = (1, 0, 0, 1), (1, 1, 1, 0)
    while n:
        if n & 1:
            result = matrix_mul(result, base, m)
        base = matrix_mul(base, base, m)
        n //= 2
    return result


def verify(path: Path) -> dict:
    envelope = json.loads(path.read_text(encoding="utf-8"))
    require(envelope["schema"] == "integer-proof-certificate-v1", "wrong schema")
    decoded = zlib.decompress(base64.b85decode("".join(envelope["payload"])))
    require(hashlib.sha256(decoded).hexdigest() == envelope["decoded_sha256"],
            "decoded certificate hash mismatch")
    data = json.loads(decoded)
    certs, composites, blocks = data["primes"], data["composites"], data["fib"]

    @lru_cache(None)
    def prime(n: int) -> bool:
        require(str(n) in certs, f"missing prime certificate: {n}")
        certificate = certs[str(n)]
        if n == 2:
            require(certificate == [], "invalid base certificate")
            return True
        require(n > 2, "invalid claimed prime")
        a, factors = certificate
        require(len({p for p, e in factors}) == len(factors), "duplicate factors")
        require(all(isinstance(p, int) and isinstance(e, int) and
                    2 <= p < n and e > 0 and prime(p) for p, e in factors),
                "invalid smaller-prime factor")
        require(prod(p**e for p, e in factors) == n-1, "incomplete n-1 product")
        require(pow(a, n-1, n) == 1, "Fermat condition failed")
        require(all(gcd(pow(a, (n-1)//p, n)-1, n) == 1 for p, e in factors),
                "full-order condition failed")
        return True

    for n in certs:
        prime(int(n))
    for ns, d in composites.items():
        n = int(ns)
        require(isinstance(d, int) and 1 < d < n and n % d == 0,
                f"invalid composite quotient witness: {n}")

    fibonacci = [0, 1]
    for _ in range(2, 397):
        fibonacci.append(fibonacci[-1] + fibonacci[-2])
    needed = {n for k in range(4, 201, 2) for n in (k, k+2, 2*(k-2))}
    require({int(n) for n in blocks} == needed, "missing or extra Fibonacci index")
    for ns, factors in blocks.items():
        n = int(ns)
        require(all(isinstance(e, int) and e >= 1 and prime(int(p))
                    for p, e in factors.items()), "invalid Fibonacci prime factor")
        require(prod(int(p)**e for p, e in factors.items()) == fibonacci[n],
                f"incomplete Fibonacci factorization: {n}")

    candidates = set()
    for k in range(4, 201, 2):
        for n in {k, k+2, 2*(k-2)}:
            for ps in blocks[str(n)]:
                p = int(ps)
                if (p-1) % k:
                    continue
                q = (p-1)//k
                if q <= 5 or str(q) in composites:
                    continue
                require(prime(q), "unclassified quotient")
                candidates.add((k, p, q))

    periods = {11:10, 13:28, 17:36, 19:18, 107:72, 2851:2850, 5443127:10886256}
    exclusions = []
    for k, p, q in sorted(candidates):
        require(q in periods, "unhandled prime-pair candidate")
        t = periods[q]
        require(fib_pair(t, q) == (0, 1), "Fibonacci return failed")
        require(q_power(t, q) == (1, 0, 0, 1), "independent matrix return failed")
        f, fp1 = fib_pair(t, p)
        require(f != 0, f"candidate not excluded: {(k, p, q)}")
        matrix = q_power(t, p)
        require(matrix[:3] == (fp1, f, f), "independent modular Fibonacci failed")
        exclusions.append([k, p, q, t, f])
    require(len(exclusions) == 10, "unexpected candidate count")
    # q=3 separately: a period is 8; F_8=21 has prime factors 3 and 7.
    require(q_power(8, 3) == (1, 0, 0, 1) and fibonacci[8] == 3*7,
            "q=3 boundary failed")
    # q=5 is excluded: p=41, k=8 is an actual counterexample to omitting it.
    require(q_power(20, 5) == (1, 0, 0, 1) and fib_pair(20, 41)[0] == 0,
            "ramified-boundary check failed")
    return {"status":"all integer certificate checks passed", "k_cases":99,
            "range":"2 <= k <= 200; all odd primes q != 5, unbounded q",
            "Fibonacci_indices":len(blocks), "largest_Fibonacci_index":396,
            "factor_primes":len({p for fs in blocks.values() for p in fs}),
            "recursive_primality_certificates":len(certs),
            "composite_quotient_certificates":len(composites),
            "exclusions_k_p_q_t_residue":exclusions, "lean_kernel_checked":False}


if __name__ == "__main__":
    print(json.dumps(verify(Path(__file__).with_name("certificate.json")), indent=2))
