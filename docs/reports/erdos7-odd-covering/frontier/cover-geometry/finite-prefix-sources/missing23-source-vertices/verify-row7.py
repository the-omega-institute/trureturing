"""Exact finite check of one allowed complete-query obstruction; no geometry."""
from fractions import Fraction as F
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


K = 27 * 5 ** 8
leaves = (4, 13, 22, 7, 16, 25)
short = (4, 13, 22)
long = (7, 16, 25)


def source(z):
    return {h: F(0) if h == 4 else F(1) - z.get(h, F(0)) for h in leaves}


def zero_depth(z):
    return {h: F(0) if h == 4 else F(2, 3) - z.get(h, F(0)) for h in leaves}


def crt(a, m, b, n):
    if m == 1:
        return b % n
    return (b + n * (((a - b) * pow(n, -1, m)) % m)) % (m * n)


layout = []
for e in range(4):
    for f in range(9):
        m, n = 3 ** e, 5 ** f
        a3, a5 = (4 if e == 2 else 0), 2 % n
        a = crt(a3, m, a5, n)
        need(a % m == a3 % m and a % n == a5, "CRT phase")
        layout.append({"modulus": m * n, "phase": a, "e3": e, "e5": f})
need(len(layout) == 36 and len({v["modulus"] for v in layout}) == 36, "one phase for every divisor")
need(all(K % v["modulus"] == 0 for v in layout), "divisor domain")
patterns = []
for h in (13, 7):
    for m in range(1, 10):
        a5 = 2 if m == 9 else 2 + 5 ** (m - 1)
        x = crt(h, 27, a5, 5 ** 8)
        need(x % 3 and x % 9 != 1 and x % 27 != 4 and x % 5 and x % 15 != 2 and x % 45 != 8, "common carrier")
        actual_m = sum(x % (5 ** f) == 2 % (5 ** f) for f in range(9))
        q = sum(x % v["modulus"] == v["phase"] for v in layout)
        indicator = h % 9 == 4
        need(actual_m == m and q == m * (1 + indicator), "complete load identity")
        hinge = max(0, q - 16)
        need(hinge == 2 * indicator * (m == 9), "threshold16 hinge identity")
        patterns.append({"row": h, "M": m, "Q": q, "hinge16": hinge})

edge = []
for u in (F(0), F(1, 2), F(1)):
    z = {13: u / 2, 22: (1 - u) / 2}
    w, wz = source(z), zero_depth(z)
    full_short, zero_short = sum(w[h] for h in short), sum(wz[h] for h in short)
    full_long, zero_long = sum(w[h] for h in long), sum(wz[h] for h in long)
    need(full_short == F(3, 2) and zero_short == F(5, 6), "closed edge short-branch mass")
    need(full_long == 3 and zero_long == 2, "closed edge long-branch mass")
    integral = 2 * full_short / K
    need(integral == F(3, K), "closed edge complete-query readout")
    edge.append({"u": str(u), "full_short": str(full_short), "zero_short": str(zero_short), "query_integral": str(integral)})

w7, wz7 = source({7: F(1, 2)}), zero_depth({7: F(1, 2)})
need(sum(w7[h] for h in short) == 2 and sum(wz7[h] for h in short) == F(4, 3), "new row7 short mass")
need(sum(w7[h] for h in long) == F(5, 2) and sum(wz7[h] for h in long) == F(3, 2), "new row7 long mass")
integral7 = 2 * sum(w7[h] for h in short) / K
need(integral7 == F(4, K) and integral7 - F(3, K) == F(1, K), "strict allowed-query separation")

print(json.dumps({
    "scope": "One selected-anchor comparison measure and one complete query; not the final live law and not a counterexample to max-query G16 domination.",
    "fixed_parameters": "(a,b,c,r,d,k)=(2,4,1,8,2,1); t1=1/20, other t=0, e=0",
    "query_period": K, "complete_divisor_count": len(layout), "query_layout": layout,
    "finite_patterns": patterns, "closed_edge_samples": edge,
    "row7_query_integral": str(integral7), "closed_edge_query_integral": str(F(3, K)),
    "strict_difference": str(F(1, K)), "ratio": "4/3",
    "zero_depth_short_mass_closed_edge": "5/6", "zero_depth_short_mass_row7": "4/3",
    "query_identity": "(Q-16)+ = 2*1_(x mod9=4)*1_(x mod5^8=2) on C",
    "transport_obstruction": "A mixture of named-anchor-preserving tree automorphisms cannot increase branch4 mass; the companion note also gives an obstruction for a specified broader positive cylinder-preserving matrix class.",
    "geometry_batches": 0,
}, sort_keys=True, indent=2))
