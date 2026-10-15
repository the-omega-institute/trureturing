---
bibkey: girlingcirstoiujennings2022unitarity
authors: Matthew Girling, Cristina Cîrstoiu, and David Jennings
year: 2022
title: "Estimation of correlations and non-separability in quantum channels via unitarity benchmarking"
doi: 10.1103/PhysRevResearch.4.023041
url: https://arxiv.org/abs/2104.04352
claim: "Appendix C.5 conjectures that the unital-block overlap of any two quantum channels is at least minus one; two qutrit coarse-graining channels have overlap minus four thirds."
strata_touched:
  - D5/S3/QuantumChannels/UnitalBlockOverlapRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1103/PhysRevResearch.4.023041

Source: https://arxiv.org/abs/2104.04352

The source is arXiv:2104.04352v3, published in *Physical Review Research* 4,
023041 (2022). Page numbers below refer to the arXiv v3 PDF.

## Liouville representation

Section II.C, page 5, states:

> We choose an orthonormal basis of operators X₀, X₁, …, X_{d²−1} for B(H_A) with X₀ = 1/√d and with respect to the Hilbert Schmidt inner product ⟨X_μ, X_ν⟩ := tr X_μ†X_ν = δ_{μ,ν}. In particular, this means that X₁, …, X_{d²−1} are all traceless operators.

The unital block consists of the positive-index entries
$T_{ij}=\operatorname{tr}(X_i^\dagger\mathcal E(X_j))$.
Its overlap is $\operatorname{tr}(T_1^\dagger T_2)$, the sum of the
conjugate products of these entries. The complex-linear matrix maps use
the existing completely-positive predicate and trace preservation on all
complex matrices.

## The conjecture and surviving bounds

Appendix C.5, page 21, after Lemma C.3, states:

> However, we conjecture a stronger result that for any two quantum channels E₁, E₂ that ⟨T₁, T₂⟩ ≥ −1.

The same paragraph states:

> Since it is not essential to our work we leave it as an open problem.

Lemma C.3 proves $-d\leq\langle T_1,T_2\rangle\leq d^2-1$.
Lemma C.4 proves the proposed lower bound when one channel is unital,
or when both channels have dimension two. The paper's nonseparability
bound uses Lemma C.3 and does not require the conjectured improvement.

## Qutrit counterexample

The repository refutation uses Kraus families $(E_{00},E_{01},E_{12})$
and $(E_{10},E_{11},E_{02})$. Both maps preserve trace and are completely
positive. Their unital-block overlap in an explicit orthonormal Hermitian
operator basis is $-4/3<-1$. This is a repository-derived refutation of
the quoted conjecture; the basis and overlap definitions follow the source.
