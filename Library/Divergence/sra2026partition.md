---
bibkey: sra2026partition
authors: Suvrit Sra
year: 2026
title: The p-Bures-Wasserstein distance via 3-by-3 block matrices (with application to p-Bures-Wasserstein barycenters)
doi: null
url: https://arxiv.org/abs/2610.15889v1
claim: Theorem 1.2 gives the all-real finite complex PSD Schatten partition inequality. The formal source uses homogeneous Carlen-Lieb trace-root convexity, positive regularization and actual Schatten Gram traces, including arbitrary rectangular free matrices.
strata_touched:
  - D5/S3/Quantum/Schatten
license: citation-only
triage: anchor
---

# Full finite Schatten partition inequality

## Verified locator

Primary source: https://arxiv.org/abs/2610.15889v1, Theorem 1.2 (Partition
inequality), equation (1.4), and Section 2 (proof by interpolation,
left inversion and the PSD regularization limit).

Sra, arXiv:2610.15889v1, Theorem 1.2 and Section 2, states that for every real
1 <= p <= 2, every arbitrary finite PSD family H_j with SPD sum H, and every
compatible complex matrix X,

sum_j ||H_j^(1/p) H^(-1/p) X||_p^p >= ||X||_p^p.

This is published mathematics. No original research solution, novelty,
unique result or original KPI is claimed (originalKPI=0).

Sra's source proof interpolates the actual row R_z between ell_1(S_1) and
ell_2(S_2), then uses its left inverse and a PSD regularization limit.
The pinned Mathlib has the actual Hadamard three-lines theorem; it does not
supply a full finite Schatten interpolation layer. The formal proof here
uses the shorter existing Carlen-Lieb route instead and does not reprove
that already formalized convexity theorem.

Put q=2/p. For invertible Z, the existing
CarlenLiebConvexity.fixed_congruence_trace_convex says that
A -> Re Tr((Z* A^q Z)^(1/q)) is convex on SPD matrices, with the spectral
power inside the trace. CFC scalar homogeneity
makes this functional homogeneous of degree one, hence subadditive.
Regularizing the PSD arguments and a PSD Z by epsilon I, and taking genuine
positive spectral-power limits, extends subadditivity to singular inputs.
Finite induction includes an empty partition.

For arbitrary rectangular X, put K=H^(-1/p), M=K XX* K and Z=sqrt(M).
Apply this trace-root subadditivity. The existing Schatten column-Gram and
row-Gram identities swap the square factors to identify each trace with
Tr((H_j^(1/p) M H_j^(1/p))^(p/2)). At H, the genuine CFC inverse powers
cancel, leaving Tr((XX*)^(p/2)). These are the actual rectangular Schatten
pth powers. The definition through schattenNorm(sqrt(XX*)) agrees with the
existing square Schatten norm and includes all zero singular values.
No finite sampling, scalar commuting reduction, assumed row bound or false
operator-valued fixed-output-Gram concavity is used.

The existing [Physlib transplant](meiburg2026schatten.md), by Alex Meiburg at
b9043cc548ef6d63a28454cf3a57fb12a0c2e142 under Apache-2.0, supplies the actual
schattenNorm, product Holder and Gram trace bridges on the consumed Hiai
proof path. Its provenance and retained license are unchanged. This unit
adds no duplicate Physlib transplant.

The new source is an analytic supplier for the unchanged Audenaert/common-Z/
three-point program; formalizing this published supplier does not finish
that original research goal. Empty row or column dimensions have zero Gram
trace; an empty SPD-sum partition is possible only in empty row dimension.
The formal statements keep every finite type and add no Nonempty premise.

The faithful dependent-family registration audit is unfinished and tracked in
[issue 26265](https://github.com/the-omega-institute/trureturing/issues/26265).
The issue is neither a proof nor a validated registration.
