#!/usr/bin/env python3
"""Wang's H6 port-filling problem: settle a branch completely, not to t <= 1000.

Han Wang, "Port Fillings for Primary Pseudoperfect Numbers", arXiv:2605.21518v1
(2026-05-18).  Section 1 notes the setting is equivalent to Erdos problem #313,
the infinitude of primary pseudoperfect numbers.  Equation (18) isolates the
port H = (R, c) = (113322, 797) coming from the prefix 2*3*11*17*101, and
equation (19) asks for B = q_1...q_6 with distinct primes q_i > 101 and

    797*B - 113322*d(B) = 1,      d(B) = sum_i B/q_i.

Such a B makes 113322*B a primary pseudoperfect number with eleven prime
factors; the known ones have at most eight.  Appendix B reports an exploratory
scan of t <= 1000 and says plainly: "These data do not exclude the branches
completely.  They show only that any completion in the displayed branches must
arise from a prefix with T > 1000."

THREE FACTS, each derived here rather than quoted.

(1) Port recursion.  With B = q*B' and d(B) = B' + q*d(B'), the filling
equation becomes (c*q - R)*B' - (R*q)*d(B') = 1, so appending q sends
(R, c) -> (R*q, c*q - R).

(2) Enumeration bounds.  Dividing the filling equation by R*B gives the exact
reciprocal identity  c/R = sum_{q | B} 1/q + 1/(R*B).  Every term is positive,
so 1/q < c/R for each q, i.e. q > R/c.  And if r primes remain, all at least q,
then sum 1/q_i <= r/q and B >= q, so c/R <= r/q + 1/(R*q), i.e.
q <= (r*R + 1)/c.  Finite and complete -- no heuristic cutoff.

(3) The last two primes are FACTORED OUT, not scanned.  For the final pair,
c*u*v - R*(u+v) = 1.  Multiplying by c and completing the product gives

    (c*u - R) * (c*v - R) = R*R + c =: N.

Both factors are positive because every final prime obeys u > R/c.  So the pair
is recovered from the divisors of one fixed integer: take d*e = N with
d = c*u - R, which forces d ≡ -R (mod c); then e ≡ -R (mod c) follows since
N ≡ R^2 (mod c).  Necessary AND sufficient -- nothing escapes into an unscanned
tail.  This is what replaces Wang's parameter scan, whose bound T reaches
1,823,798,450,784 on this branch.

Wang's Section 16 bound is kept as the cheap pre-filter: with P0 = c^{-1} mod R,
S0 = (c*P0 - 1)/R and U = max(m+1, floor(R/c)+1), the admissible parameters obey
0 <= t <= (U^2 - S0*U + P0)/(c*U - R), and c*U - R > 0 always, so a negative
numerator means no completion at all.

LADDERS.  Both must pass or no emptiness claim here stands.
  * Control: run the pair-finder on the base port (113322, 797) with primes
    > 101 and recover Wang's own filling 149 * 3109 (his Section 17).
  * Table 2: the branch counts must reproduce Wang's published figures for
    q1 in {389, 397, 401, 409}.  My enumeration is a deliberate superset -- the
    bounds above are slightly looser than his reciprocal-capacity pruning -- so
    the prefix totals run a few thousand high, and every extra lands in T < 0.
    The two columns that matter, 0 <= T <= 1000 and T > 1000, must match exactly.

Usage:
    wang-h6-port-filling.py                 ladders only (seconds)
    wang-h6-port-filling.py count Q1 ...    branch census, no settling
    wang-h6-port-filling.py settle Q1 ...   settle every T >= 0 prefix
"""

from __future__ import annotations

import sys
import time

from sympy import divisors, isprime, primerange

PORT_R, PORT_C = 113322, 797
NPRIMES = 6

# Wang, Appendix B, Table 2: q1 -> (prefixes, T<0, 0<=T<=1000).
WANG_TABLE2 = {
    409: (1156527, 1047472, 98398),
    401: (1209161, 1157101, 48832),
    397: (1215077, 1194620, 19190),
    389: (1527289, 1419120, 99337),
}


def completions(R: int, c: int, qlast: int) -> list[tuple[int, int]]:
    """Every pair of primes qlast < u < v completing the port (R, c)."""
    n_fixed = R * R + c
    out = []
    for d in divisors(n_fixed):
        e = n_fixed // d
        if d > e:
            break
        if (d + R) % c or (e + R) % c:
            continue
        u, v = (R + d) // c, (R + e) // c
        if u > qlast and u < v and isprime(u) and isprime(v):
            out.append((u, v))
    return out


def branch(q1: int, settle: bool, report: int = 2000):
    """Census (and optionally settlement) of the q1 branch."""
    stats = {"prefixes": 0, "neg": 0, "small": 0, "big": 0}
    fillings: list[tuple[list[int], list[tuple[int, int]]]] = []
    started = time.time()

    def walk(chosen, R, c, last, remaining):
        if len(chosen) == 4:
            stats["prefixes"] += 1
            p0 = pow(c, -1, R)
            s0 = (c * p0 - 1) // R
            u = max(last + 1, R // c + 1)
            num = u * u - s0 * u + p0
            if num < 0:
                stats["neg"] += 1
                return
            stats["small" if num // (c * u - R) <= 1000 else "big"] += 1
            if settle:
                found = completions(R, c, last)
                if found:
                    fillings.append((list(chosen), found))
                    print(f"*** FILLING {chosen} -> {found}", flush=True)
                done = stats["small"] + stats["big"]
                if done % report == 0:
                    print(f"  settled {done}  scanned {stats['prefixes']}  "
                          f"{time.time() - started:.0f}s", flush=True)
            return
        lo, hi = R // c, (remaining * R + 1) // c
        start = max(lo + 1, last + 1)
        if hi < start:
            return
        for q in primerange(start, hi + 1):
            walk(chosen + [q], R * q, c * q - R, q, remaining - 1)

    walk([q1], PORT_R * q1, PORT_C * q1 - PORT_R, q1, NPRIMES - 1)
    return stats, fillings, time.time() - started


def ladders() -> int:
    bad = []
    got = completions(PORT_R, PORT_C, 101)
    ok = (149, 3109) in got
    print(f"control: base port completions {got} -> contains Wang's 149*3109: "
          f"{'PASS' if ok else 'FAIL'}")
    if not ok:
        bad.append("control lost Wang's own filling")
    for q1, (w_pref, w_neg, w_small) in sorted(WANG_TABLE2.items()):
        stats, _, secs = branch(q1, settle=False)
        w_big = w_pref - w_neg - w_small
        hit = stats["small"] == w_small and stats["big"] == w_big
        print(f"  q1={q1}: 0<=T<=1000 {stats['small']} (Wang {w_small}), "
              f"T>1000 {stats['big']} (Wang {w_big}), "
              f"prefixes {stats['prefixes']} (Wang {w_pref}, superset by "
              f"{stats['prefixes'] - w_pref}) -> {'PASS' if hit else 'FAIL'} "
              f"[{secs:.0f}s]")
        if not hit:
            bad.append(f"q1={q1} disagrees with Table 2")
    for msg in bad:
        print(f"LADDER FAILURE: {msg}")
    return 1 if bad else 0


def main() -> int:
    if len(sys.argv) == 1:
        return ladders()
    mode, targets = sys.argv[1], [int(x) for x in sys.argv[2:]]
    if mode not in {"count", "settle"} or not targets:
        print(__doc__.rsplit("Usage:", 1)[-1])
        return 2
    got = completions(PORT_R, PORT_C, 101)
    if (149, 3109) not in got:
        print("LADDER FAILURE: control lost Wang's own filling; results void")
        return 1
    print("control PASS", flush=True)
    for q1 in targets:
        stats, fillings, secs = branch(q1, settle=(mode == "settle"))
        print(f"q1={q1} prefixes {stats['prefixes']} T<0 {stats['neg']} "
              f"0<=T<=1000 {stats['small']} T>1000 {stats['big']} "
              f"fillings {len(fillings)} [{secs:.0f}s]", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
