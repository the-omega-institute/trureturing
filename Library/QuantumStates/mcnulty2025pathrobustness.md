---
bibkey: mcnulty2025pathrobustness
authors: Daniel McNulty
year: 2025
title: "A Graph-Theoretic Approach to Quantum Measurement Incompatibility"
doi: null
url: https://arxiv.org/abs/2511.15954
claim: "Conjecture 1 asserts that every path P_{2n}, path P_{2n+1} and even cycle C_{2n+2} has incompatibility robustness (2/(2n+2)) csc(pi/(2n+2)), for n >= 1."
strata_touched:
  - D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness
license: citation-only
triage: anchor
---

# Path robustness of binary quantum observables

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2511.15954

The source is arXiv:2511.15954v1. Definition 1 and the robustness
definition, Eqs. (8)–(10), are on p. 3. Conjecture 1 is on p. 9,
Section V.B.5, “Paths”. Crossref's title-and-author search has no matching
record for this preprint.

Definition 1, p. 3:

> The *anti-commutativity graph* $G = (V,E)$ of a set of observables
> $\mathcal{A}$ is defined by $\{v,v'\}\in E \iff A_vA_{v'}=-A_{v'}A_v,$
> so that adjacent vertices correspond to anti-commuting observables,
> and non-adjacent vertices correspond to commuting ones.

Binary effects, p. 2, Eq. (3):

> $M_v(\pm)=\frac12(\mathbb{1}\pm A_v).$

Joint measurability, p. 3, Section II.C:

> A collection of measurements are jointly measurable if there exists a parent POVM such that each measurement can be recovered as one of its marginals, or equivalently, if their statistics can be obtained from the parent after classical post-processing [47, 48].

Robustness, p. 3, Eqs. (8)–(9):

> $\eta(G)\equiv \max\{\eta\in[0,1]\,|\,\mathcal{A}^{\eta}\text{ is jointly measurable}\},$
> where $\mathcal{A}^{\eta}=\{A_v^{\eta}\,|\,v\in V\},\quad
> A_v^{\eta}=\eta A_v+\frac{\operatorname{tr}[A_v]}{d}(1-\eta)\mathbb{1},$
> are noisy (unsharp) versions of the original observables with
> anti-commutativity graph $G$.

Conjecture 1, p. 9:

> For all $n\geq 1$, paths satisfy
> $\eta(P_{2n})=\eta(P_{2n+1})=\eta(C_{2n+2})=
> \frac{2}{2n+2}\csc\Big(\frac{\pi}{2n+2}\Big)\,.$

The observables are Hermitian involutions on a finite-dimensional
complex Hilbert space. The matrix encoding uses `Fin d` coordinates
with `1 ≤ d`, Mathlib's `pathGraph` and `cycleGraph`, and the literal
trace term in the noisy observable. A joint parent is indexed by
Boolean assignments, with `true` denoting the positive sign; both
signed marginals are exact. Greatest feasible visibility is expressed
by `IsGreatest` on the feasible subset of `[0,1]`.
