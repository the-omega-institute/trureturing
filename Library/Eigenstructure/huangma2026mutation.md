---
bibkey: huangma2026mutation
authors: Min Huang and Qiling Ma
year: 2026
title: A mutation invariant for skew-symmetrizable matrices
doi: 10.1016/j.jalgebra.2026.07.040
url: https://arxiv.org/abs/2602.03194v1
claim: "Remark 2.7 conjectures that for fixed n and a fixed positive skew-symmetrizer, the delta invariant is binary."
strata_touched:
  - D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant
license: citation-only
triage: anchor
---

# A mutation invariant for skew-symmetrizable matrices

## Verified locator

DOI: 10.1016/j.jalgebra.2026.07.040

Source: https://arxiv.org/abs/2602.03194v1

The quotations refer to arXiv v1. The journal citation is Journal of Algebra 712 (2027), 546–558. Whether the journal text changes Remark 2.7 is ASSUMED-UNVERIFIED.

## Source statements

Section 1, p. 1:

> A matrix B = (b_ij) ∈ M_n(Z) is called skew-symmetrizable if there exists a diagonal matrix D = diag(d_1, …, d_n) with positive integers d_i such that DB is skew-symmetric. Such a matrix D is called a skew-symmetrizer of B.

Section 1, p. 2:

> we define its symmetrization to be the symmetric matrix S(B) = (s_ij) ∈ M_n(R) given by s_ij = 2 if i = j, s_ij = sgn(b_ij)√|b_ij b_ji| if i < j, s_ij = sgn(b_ji)√|b_ij b_ji| if i > j, where sgn(x) denotes the sign of x, with the convention sgn(0) = 0.

Definition 1.3, p. 2:

> The δ-invariant of a skew-symmetrizable matrix B ∈ M_n(Z) is defined as δ(B) := det(S(B)) (mod 4)

Remark 2.7, p. 7:

> We also conjecture that for any fixed n and any choice of skew-symmetrizer d₁, …, dₙ, the invariant δ is binary. This is supported by several explicit computations.

The integer matrix uses the ordered index set Fin n. A positive natural vector d expresses the diagonal skew-symmetrizer. The real symmetrization uses Int.sign, real absolute value and Real.sqrt. Binary means at most two residues in ZMod 4; the residues can coincide. An existential integer determinant records Lemma 1.2 along with the residue assertion. The formal statement also includes the empty matrix.

## Scope

The exact existential binary claim and the odd-size residue set are proved in the Lean module. The even-size argument uses a signed companion-determinant congruence and the square class of the weighted alternating determinant. It does not identify an explicit residue in terms of the valuation and odd part of the weight product, or classify when both residues occur.

The experiment in `the-omega-institute/trureturing-experiments`, `docs/reports/huang-ma-2026-remark-2-7-binary-delta/`, has commit `2d7247cb9a8d67c172b5755a8fd40e027e8c4c93` and `check.py` SHA-256 `15b654701057c742fe05c7b76fe489d9e5b888466e8a8fd54fede32b7949cd50`. The recorded command `python3 check.py` exited 0 with `RESULT PASS`. These computations are distinct from the Lean proof. Literature completeness remains ASSUMED-UNVERIFIED.
