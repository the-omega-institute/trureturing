---
bibkey: hwangkim2024nearorder
authors: Jinmi Hwang; Sejong Kim
year: 2024
title: Near-order relation of power means
doi: 10.1007/s11117-024-01099-4
url: https://arxiv.org/abs/2407.07438v1
claim: "The final unnumbered question in Section 6 asks whether LE(ω; 𝔸) ≼ Ω(ω; 𝔸) for positive definite matrices and strictly positive probability weights."
strata_touched:
  - D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation
license: citation-only
triage: anchor
---

# Near-order relation of power means

## Verified locator

DOI: 10.1007/s11117-024-01099-4

Source: https://arxiv.org/abs/2407.07438v1

The source version is arXiv:2407.07438v1. The DOI identifies the journal
publication in *Positivity* 29, article 3. Agreement of the journal body with
the arXiv question is ASSUMED-UNVERIFIED; the statement below is read from v1.

## Source statement

Page 17, Section 6, final paragraph:

> It would be an interesting problem to study whether the weak log-majorization relation generalizes to the near-order or entrywise eigenvalue relation. Note that (6.21) is a generalization of (4.14). From this point of view, we give an open question:

$$
\mathrm{LE}(\omega; \mathbb{A}) \preceq \Omega(\omega; \mathbb{A}).
$$

This display is unnumbered. Equation (6.21) is the harmonic–log-Euclidean–arithmetic
comparison. The near-order question is distinct from the entrywise eigenvalue
question in the preceding sentence.

Page 5, equation (3.5): “For $A,B\in\mathbb P$,” followed by
“$A\preceq B$ if and only if $A^{-1}\#B\geq I$.” Page 9, equation (4.10),
defines $\exp(\sum_{j=1}^{n}w_j\log A_j)=:\mathrm{LE}(\omega;\mathbb A)$.
The inputs are
complex positive definite matrices and the weights are strictly positive and
sum to one. Page 4, Section 2: “where

$$
d_W(A,B)=\left[\operatorname{tr}(A+B)-
2\operatorname{tr}(A^{1/2}BA^{1/2})^{1/2}\right]^{1/2}.
$$

is the Bures-Wasserstein distance of $A,B\in\mathbb P_m$.”

The multivariable least-squares definition used for $\Omega$ is equation (2)
of Bhatia, Jain and Lim, *Inequalities for the Wasserstein mean of positive
definite matrices*, https://arxiv.org/abs/1803.03357. The positive definite
minimizer is unique for admissible inputs; the Lean definition uses
`Classical.epsilon` on the literal minimizer predicate. On page 1 the source
states:

> Let $A_1,\dots,A_m$ be given positive definite matrices and let $w=(w_1,\dots,w_m)$ be a vector of weights; i.e., $w_j\geq0$ and $\sum_{j=1}^m w_j=1.$ Then the (weighted) Wasserstein mean, or the Wasserstein barycentre of $A_1,\dots,A_m$ is defined as

$$
\Omega(w;A_1,\ldots,A_m)=\underset{X\in\mathbb P}{\arg\min}
\sum_{j=1}^{m}w_j d^2(X,A_j).
$$

The Lean encoding uses $n$ for the number of inputs, $m$ for the matrix
dimension, and `Fin n` for the input indices.

## Scope

The refutation uses two positive definite $2\times2$ matrices and equal
weights. It disproves the universal near-order comparison. It does not
refute weak log-majorization or settle the separate entrywise-eigenvalue
question. Completeness of the literature screen and priority beyond the
sources read on issue #21282 are ASSUMED-UNVERIFIED.

## Revision2 companion source and credits

The complete scientific follow-up is Ma–Zhang, *Counterexamples beyond
Bhatia–Jain–Lim (2018): Hwang–Kim's near-order question and its entrywise
companion*, revision2, dated 9 November 2026, CC BY 4.0. Haobo Ma is
affiliated with ChronoAI, Singapore; Wenlin Zhang with the National
University of Singapore and ChronoAI, Singapore. No Omega affiliation is
claimed. [Whole-source intake and approved outcome plan](https://github.com/the-omega-institute/trureturing/issues/29594)
retain all eight scientific groups and the verified primary-source supplement.
The selected `note.tex` SHA-256 is
`d028aeda7d86580083b2e522cc52c7075d9b42cb79d2dc847987ed5fa686c839`.
The manuscript handoff release is custody of existing research, not evidence
of a new scientific publication or priority.

The source includes both explicit witnesses, a finite positive-weight
transport minimizer lemma, the exact 2D iff, commuting comparison and
equality, suitable-chosen-positive-weight extensions to all matrix sizes
and input counts at least two, and the stated reverse consequences.
These must not be conflated with the scope of the original `result`.
The original all-$r$ analytic rotation family and full classification of
reverse implications remain open. Finite exact checker output is not a
kernel proof of those families. Literature and priority limitations from
the original record remain in force.
