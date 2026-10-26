---
bibkey: ikhlefmorinduchesne2024fusion
authors: Yacine Ikhlef and Alexi Morin-Duchesne
year: 2024
title: "Fusion of irreducible modules in the periodic Temperley–Lieb algebra"
doi: 10.21468/SciPostPhys.17.5.132
url: https://arxiv.org/abs/2312.14837v2
claim: "Appendix C, Conjectures C.1 and C.2, gives product evaluations of the seed recurrences at y = εq^m."
strata_touched:
  - D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.21468/SciPostPhys.17.5.132

Source: https://arxiv.org/abs/2312.14837v2

## Source statements

Y. Ikhlef and A. Morin-Duchesne, "Fusion of irreducible modules in the periodic Temperley–Lieb algebra", arXiv:2312.14837v2 (3 September 2024); SciPost Phys. 17, 132 (2024), DOI 10.21468/SciPostPhys.17.5.132.

- **Proposition C.1.** X^{(p)}_m(ω, x, y) "is a polynomial in the variables α_a = x + x⁻¹, α_b = y + y⁻¹ and α_ω = ω + ω⁻¹, that satisfies the recursion relation for m ⩾ p + 1: X_{m+1} = (α_a + α_pα_bα_ω/({m}{m+1})) X_m + (α_p² − {m}²)(α_b² − {m}²)(α_ω² − {m}²)/((q − q⁻¹)²[2m − 1][2m + 1]{m}²) X_{m−1} (C.3) and the initial conditions X_p = 1, X_{p+1} = α_a + α_bα_ω/{p + 1} (C.4), where α_p = q^p + q^{−p} and {m} = q^m + q^{−m}."
- **Conjecture C.1.** "For p ⩾ 1, the function X^{(p)}_m(ω, x, y) specialised to y = εq^m evaluates to X^{(p)}_m(ω, x, εq^m) = (ωx)^{p−m} ∏_{r=−(m−p−1)/2}^{(m−p−1)/2} (xq^{2r} + εω)(εq^{2r} + xω). (C.5) … we verified explicitly that Conjecture C.1 holds for m = p, p+1, …, p+7."
- **Proposition C.2 / Conjecture C.2.** The seed states σ^{(0)}_{0,m} satisfy σ_{m+1} = (α_a + 2α_bα_{ab}/({m}{m+1}))σ_m − [m]²(α_b² − {m}²)(α_{ab}² − {m}²)/([2m + 1][2m − 1]{m}²)σ_{m−1} (C.24), σ_0 = 1, σ_1 = α_a + α_bα_{ab}/{1} (C.25), and "The intermediate seed states σ^{(0)}_{0,m}(w, x, y) specialised to y = εq^m evaluate to σ^{(0)}_{0,m}(w, x, εq^m) = (wx)^{−m} ∏_{r=−(m−1)/2}^{(m−1)/2} (xq^{2r} + εw)(εq^{2r} + xw). (C.26) … we checked that Conjecture C.2 holds for m = 0, 1, …, 7."

Proposition C.1 and (C.3)–(C.4) are on page 61; Conjecture C.1 and (C.5) are on page 62. Proposition C.2, Conjecture C.2 and (C.24)–(C.26) are on page 65.

The definition sentences are: "where X^{(p)}_m(ω, x, y) is a polynomial in the variables α_a = x + x^{−1}, α_b = y + y^{−1} and α_ω = ω + ω^{−1}, that satisfies the recursion relation for m ⩾ p + 1" (p. 61), "where α_p = q^p + q^{−p} and {m} = q^m + q^{−m}." (p. 61), and "The seed states σ^{(0)}_{0,m} with m ⩾ 0 are polynomials in α_a = x + x^{−1}, α_b = y + y^{−1} and α_{ab} = w + w^{−1} that satisfy the linear system for m ⩾ 1" (p. 65).

The product index advances in unit steps, so for N factors it has integer exponent 2r = −N+1+2j, with j = 0,…,N−1. The Lean function seedX q x y w p n denotes X^{(p)}_{p+n}(w,x,y); seedSigma transcribes (C.24)–(C.25) independently. The statement uses nonzero complex q,x,w, non-root-of-unity q, and ε = ±1. It asserts (C.5) for every 1 ≤ p ≤ m and (C.26) for every natural m.

The proof identifies the seed recurrence with a monic Askey–Wilson recurrence and uses a coupled Darboux shift. A vanishing terminal coefficient yields the finite product. The p=0 recurrence equals the separately transcribed sigma recurrence. This proves the evaluations relative to the published recurrences; it does not formalize the representation-theoretic fusion decompositions of Section 4.

The exact experiment is in the-omega-institute/trureturing-experiments, docs/reports/ikhlef-morin-duchesne-2024-seed-state-specialisation, commit 9c938126e2a42c193e8fcc5db1abb1c4b2f1f847. The source check.py has SHA-256 2212a263301dd747c64b084e29a8b2d0ce2dd3b09ca097f5b1b3bd438903be81; issue #18569 records exit 0 and RESULT PASS.

Literature completeness is ASSUMED-UNVERIFIED. The literature screen on #18569 reports no settlement in the cited later papers. Roots of unity and a finite-horizon weakening of the non-root condition remain open here.
