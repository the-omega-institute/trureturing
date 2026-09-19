"""Exact checks for the actual-union / prefix-cap saturation family.

This is a finite verifier of the displayed construction, not a universal proof.
No assertion statement is used: checks remain enabled under python -O.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from math import gcd


def require(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def check(Q, p, H, exhaustive=False):
    require(Q > 1 and H >= 1 and gcd(Q, p) == 1, "input range")
    N = p ** H
    alpha = F(1, N)
    delta = alpha / 2
    # On old x=0 the actual forbidden mixed class 0 mod Q*p^H is y=0.
    K = [F(1, N) * ((alpha - delta) / (alpha * (1 - delta))
                    if y == 0 else 1 / (1 - delta)) for y in range(N)]
    require(sum(K) == 1, "kernel mass")
    b = K[0]
    require(b == (alpha - delta) / (1 - delta) and b > 0, "actual deletion charge")
    A = F(0)
    for t in range(1, H + 1):
        C = p ** t
        masses = [sum(K[y] for y in range(N) if y % C == r) for r in range(C)]
        cap = F(1, C) / (1 - delta)
        require(max(masses) == cap, "prefix cap attained")
        require(masses[1] == cap, "common nested path attains cap")
        require(any(all(y != 0 for y in range(N) if y % C == r)
                    for r in range(C)), "empty forbidden prefix")
        A += (2 * t + 1) * cap
    tau = len(divisors(Q))
    loads = [tau * (1 + sum(y % (p ** t) == 1 for t in range(1, H + 1)))
             for y in range(N)]
    attained = sum(K[y] * loads[y] ** 2 for y in range(N))
    upper = tau ** 2 * (1 + A)
    require(attained == upper, "full actual-layout transfer equality")
    energy = sum(F(1, N) * (N * k - 1) ** 2 for k in K)
    require(energy == delta ** 2 * (1 - alpha) / (alpha * (1 - delta) ** 2),
            "positive distortion energy")
    require(energy > 0, "energy is nonzero despite zero transfer rebate")
    count = 0
    if exhaustive:
        mods = divisors(Q * N)
        # CRT x_old=0 and y_new=y; evaluate every literal residue layout.
        points = [next(z for z in range(Q * N) if z % Q == 0 and z % N == y)
                  for y in range(N)]
        best = F(0)
        for layout in product(*(range(d) for d in mods)):
            value = sum(K[y] * sum(points[y] % d == a for d, a in zip(mods, layout)) ** 2
                        for y in range(N))
            best = max(best, value)
            count += 1
        require(best == upper, "exhaustive Gamma agrees")
    print(f"Q={Q}, p={p}, H={H}: Gamma={upper}, b={b}, energy={energy}; "
          f"all prefix and transfer equalities passed; exhaustive_layouts={count}")


if __name__ == "__main__":
    for Q, p, H in [(3, 5, 1), (5, 3, 1), (3, 7, 1)]:
        check(Q, p, H, exhaustive=True)
    for Q, p, H in [(9, 5, 2), (15, 7, 3), (45, 11, 2), (35, 3, 4)]:
        check(Q, p, H)
