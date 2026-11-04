---
bibkey: guojin2025measure
authors: Y. Guo; Z.-X. Jin
year: 2025
title: "Measure of entanglement and the monogamy relation: a topical review"
doi: 10.48550/arXiv.2512.21992
url: https://arxiv.org/abs/2512.21992v1
claim: "Section 9.4 conjectures that the maximal single-party reduced function does not increase on average under LOCC; Table 16 includes von Neumann entropy."
strata_touched:
  - D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC
license: citation-only
triage: anchor
---

# Maximum single-party entropy and local measurements

## Verified locator

DOI: 10.48550/arXiv.2512.21992

Source: https://arxiv.org/abs/2512.21992v1

The source is version 1, dated 26 December 2025.

## Source statements

Section 2, p. 14:

> S(ρ) = −Tr(ρ log₂ ρ) is the von Neumann entropy of the state ρ

Section 9.4, Eq. (189), pp. 87–88:

> The quantity E′^(n)(|ψ⟩) = max_i h(ρ^{A_i}) can reports the amount of entanglement contained in |ψ⟩ to some extent [168]: If it is nonincreasing on average under LOCC, then (i) E′^(3) is a complete global MEM but not tightly complete monogamous, and if h is strictly concave, E′^(3) is completely monogamous, and (ii) E′^(n) is not complete whenever n ≥ 4.

Section 9.4, p. 88:

> Note here that we can not prove here E′^(n) is nonincreasing on average under LOCC, but we conjecture that E′^(n) does not increase on average under LOCC for these cases mentioned above. Hereafter we always assume the conjecture is true.

Table 16 includes h = S. The formal claim takes amplitudes on `Fin n → Fin d`, uses the coordinate partial trace, and encodes the consequence for one local Kraus measurement whose adjoint products sum to the identity. Zero-probability branches contribute zero. The operator logarithm is `CFC.log` on `CStarMatrix`; division by `Real.log 2` gives entropy in bits.

## Counterexample and boundary

For four parties of local dimension nine, the amplitude is 1/4 on the sixteen tuples `(0,0,j,j)` and `(j,j,0,0)`, for j from 1 to 8, and zero elsewhere. Each initial single-party entropy equals 5/2. Measuring whether the first party is zero gives two outcomes with probability 1/2. Each normalized outcome has a single-party entropy of 3, on a party that depends on the outcome. Thus the average maximum is at least 3 and exceeds 5/2. The Lean result proves this lower bound and the refutation; it does not prove the corresponding upper bounds or the three-party conjecture.

The numerical experiment is [check.py at d05903467105c17132f8eef4a51b8fbc5f5dcf98](https://github.com/the-omega-institute/trureturing-experiments/blob/d05903467105c17132f8eef4a51b8fbc5f5dcf98/docs/reports/guo-jin-2025-max-marginal-entropy-locc/check.py), SHA-256 `4617e83628541864bd1accdbe6f4251f35ce025c93de9fe891ebbf12801520ad`. Issue #20726 records `python3 check.py`, exit 0. Its family calculations and the observations for other reduced functions are numerical evidence.

## Literature boundary

The literature screen in [#20726](https://github.com/the-omega-institute/trureturing/issues/20726) identifies the same conjecture in arXiv:2301.00334v3 and no settlement in the inspected portions of arXiv:2605.22150v1 and arXiv:2608.28985v1. The erratum and those later papers were not read in full. Completeness is ASSUMED-UNVERIFIED. Conditional three-party consequences are not independently refuted by the four-party counterexample.
