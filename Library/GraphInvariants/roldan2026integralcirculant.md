---
bibkey: roldan2026integralcirculant
authors: D. G. Roldán
year: 2026
title: Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3
doi: 10.48550/arXiv.2604.09491
url: https://arxiv.org/abs/2604.09491v1
claim: Conjecture 1.3 states that D* = {1, p^2, pq, q^2, p^2q^2, pq^3} uniquely maximises the integral circulant energy at n = p^2q^3 for distinct odd primes p and q.
strata_touched:
  - D5/S3/Arith/RoldanCirculantEnergyP2Q3
  - D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate
license: citation-only
triage: anchor
---

# Integral circulant energy at order p²q³

## Verified locator

DOI: 10.48550/arXiv.2604.09491

Source: https://arxiv.org/abs/2604.09491v1

Version 1, page 3, Section 1, Conjecture 1.3 (Universality).

> For every pair of distinct odd primes (p, q), the set D* = {1, p^2, pq, q^2, p^2q^2, pq^3} is the unique maximiser of E(p^2q^3, D) over all nonempty D ⊆ div(p^2q^3) ∖ {p^2q^3}.

Page 1, Section 1 defines the graph and its energy:

> An integral circulant graph ICG(n, D) has vertex set Z_n and connects a and b whenever gcd(a − b, n) ∈ D, where D is a nonempty set of proper divisors of n.

> E(G) = Σ_{i=1}^n |λ_i|, where λ_1, …, λ_n are the eigenvalues of its adjacency matrix.

The Lean representation uses `Fin n` with subtraction modulo n, the real adjacency matrix, and the real roots of its characteristic polynomial with multiplicity. Its energy is the sum of the absolute values of those roots. The set of allowed divisors is `Nat.properDivisors`.

The repository proof diagonalizes the circulant, groups frequencies by their gcd with n, and evaluates prime-power Ramanujan sums. In the variables u = p − 3 and v = q − 3, a finite coefficient certificate bounds all competing divisor sets strictly below D*. Both variables may be zero, so the argument includes q = 3.

## Literature boundary

The literature screen in issue #19144 reads this source and Jiang–Yang, arXiv:2608.29523v1, whose q ≥ 5 theorem leaves q = 3 uncovered. Completeness of the literature screen is ASSUMED-UNVERIFIED.

## Independent computation

The experiment is `docs/reports/roldan-2026-icg-energy-p2q3/` in `the-omega-institute/trureturing-experiments`, commit `931fed54e9a0f090cb4d77b00ef05b78581d8482`. The `check.py` bytes agree with that commit and have SHA-256 `7e5e620660c968566401ade3a1bfa4994eace8bc27f27e6518cdeb02a275143d`; `python3 check.py` exits 0 with `RESULT PASS`. This computation is separate from Lean proof evidence.
