---
bibkey: alcarazramos2024conformaltower
authors: Francisco C. Alcaraz, Lucas M. Ramos
year: 2024
title: "Conformally invariant free parafermionic quantum chains with multispin interactions"
doi: 10.1103/PhysRevE.109.044138
url: https://arxiv.org/abs/2402.09936v3
claim: "The homogeneous N=3 chain is predicted to satisfy M ε_i → π(2√3)(7/6+i−1) along M=3m for each fixed i≥1."
strata_touched:
  - D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation
license: citation-only
triage: anchor
---

# Alcaraz–Ramos conformal quasienergy prediction

## Verified locator

DOI: 10.1103/PhysRevE.109.044138

Source: https://arxiv.org/abs/2402.09936v3

The version is v3, 22 August 2024; the journal reference is Physical Review E **109**, 044138. The PDF uses consecutive equation numbers: (26)–(27), (38), (39) and (41) correspond to the source TeX labels (3.11)–(3.12), (4.7), (4.8) and (4.10).

## Source statements

Page 4, Eqs. (26)–(27): “P_M^{(N)}(z) = P_{M−1}^{(N)}(z) − zλ_M^N P_{M−N}^{(N)}(z),” followed by “with the initial condition” and “P_M^{(N)}(z) = 1, for M ≤ 0,”. Immediately before Eq. (26): “Apart from the zero modes they are given by Λ_k = 1/z_k^{1/N}, where z_k are the roots (P_M^{(N)}(z_k)=0) of the characteristic polynomial”.

Page 5, Eq. (38), continuing on page 6: “1/z_i^{1/N} = ε_i = π A_i^{(N)}/M = π A^{(N)}/M (x_s^{(N)} + i − 1),” and “for i = 1, 2, …”. Page 6: “Our numerical solutions for polynomial roots with M up to 10⁹ corroborate the conformal invariance prediction (38) for the roots. We conjecture the following exact values for N = 2, 3, 4 and 6”. Eq. (39) includes “A^{(3)} = 2√3”; Eq. (41) includes “x_s^{(3)} = 7/6 (mod(M,3)=0)”.

## Mathematical scope

The Lean definitions specialize the polynomial recurrence to N=3 and λ_j=1. The index shift is poly(n)=P_{n−2}. Positive roots are sorted in decreasing order, with multiplicity, and quasienergy(M,i) is the inverse cube root of entry i−1; absent indices have value zero. The claim reads the source's leading behaviour as convergence of M ε_i for each fixed i≥1 along M=3m.

The repository refutation uses i=1. It obtains the scaled finite-sum limit F(u)=Σ_{k≥0}(−1)^k u^{3k}/(3k+2)! and proves that F is positive on [4.2321,4.2323], which contains 7π/(3√3). A predicted limiting quasienergy would force F to vanish there. Existence and the exact value of the actual lowest-mode limit are outside this formal conclusion.

The literature screen recorded in issue #19220 found no settlement among the source versions, the listed later works and the reachable citing papers. Its completeness is ASSUMED-UNVERIFIED.
