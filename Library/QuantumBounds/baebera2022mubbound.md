---
bibkey: baebera2022mubbound
authors: J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty
year: 2022
title: "How many mutually unbiased bases are needed to detect bound entangled states?"
doi: 10.1088/1751-8121/acaa16
url: https://arxiv.org/abs/2108.01109
claim: "Equation (4) defines the MUB entanglement witness; Conjecture 1 predicts that the minimal number of MUBs for bound entanglement detection in dimension d = 2^r, r > 1, is d/2 + 1."
strata_touched:
  - D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation
license: citation-only
triage: anchor
---

# MUB witnesses and the power-of-two resource conjecture

J. Bae, A. Bera, D. Chruściński, B. C. Hiesmayr and D. McNulty,
*How many mutually unbiased bases are needed to detect bound entangled states?*,
Journal of Physics A: Mathematical and Theoretical 55 (2022), 505303.
Page numbers refer to arXiv:2108.01109v2.

## Verified locator

DOI: https://doi.org/10.1088/1751-8121/acaa16

Source: https://arxiv.org/abs/2108.01109

Version: https://arxiv.org/pdf/2108.01109v2

## Source statements

Section I, p. 2:

> Generalising to larger collections of measurements, we say a set of bases is mutually unbiased if all bases are pairwise unbiased.

Section VIII, p. 8:

> When d = 2^r, we predict that d/2 + 1 MUBs are both necessary and sufficient for the witness W^Γ(M_m, s) to be non-decomposable.

> Conjecture 1. If d = 2^r and r > 1, the minimal number of MUBs required for bound entanglement detection equals m = d/2 + 1 = 2^{r−1} + 1.

Section II, Eq. (4), p. 3:

$$
W(\mathcal M_m,s)=\frac{d+m-1}{d}\,\mathbb 1\otimes\mathbb 1-B(\mathcal M_m,s).
$$

The computational-basis contribution to $B$ pairs $\ell$ with $\ell+s$
modulo $d$. Each remaining basis contributes the sum of equal-column
rank-one tensor projectors. Partial transposition conjugates the second
projector, giving $W^\Gamma(\mathcal M_m,s)$.

## Scope

The Lean claim expresses the necessity half: no family with fewer than
$2^{r-1}+1$ bases detects a positive-partial-transpose density matrix through
this witness. The refutation uses $r=3$, four bases and shift $s=1$.
It does not assert that four is the minimum. Theorem 1's sufficiency for
$m>d/2+1$ is a separate source result.
