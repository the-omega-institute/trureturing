---
bibkey: debievre2023incompatibility
authors: Stephan De Bièvre
year: 2023
title: "Relating incompatibility, noncommutativity, uncertainty and Kirkwood-Dirac nonclassicality"
doi: 10.1063/5.0110267
url: https://arxiv.org/abs/2207.07451v1
claim: "For every dimension d ≥ 4, noncommutativity of every pair of nontrivial coordinate projectors does not imply complete incompatibility of two orthonormal bases (§5, conjecture following Proposition 7)."
strata_touched:
  - D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible
license: citation-only
triage: anchor
---

# Noncommuting coordinate projectors and complete incompatibility

Stephan De Bièvre, J. Math. Phys. 64, 022202 (2023), arXiv:2207.07451v1.
The page numbers below refer to the arXiv version.

Section 3, p. 5 defines the coordinate orthogonal projectors by

$$
\Pi_{\mathcal A}(S)=\sum_{i\in S}|a_i\rangle\langle a_i|,
\qquad \Pi_{\mathcal B}(T)=\sum_{j\in T}|b_j\rangle\langle b_j|.
$$

Definition 4, p. 14:

> We say that two bases $\mathcal A$ and $\mathcal B$ are completely incompatible
> (COINC) if and only if all index sets $S,T$ in $\llbracket1,d\rrbracket$ for
> which $|S|+|T|\leq d$ have the property that
> $\Pi_{\mathcal A}(S)\mathcal H\cap\Pi_{\mathcal B}(T)\mathcal H=\{0\}$.

Proposition 7(ii), p. 16:

> For all $S,T\subset\llbracket1,d\rrbracket$, with $1\leq |S|,|T|<d$,
> $[\Pi_{\mathcal A}(S),\Pi_{\mathcal B}(T)]\not=0$.

Section 5, p. 16:

> We conjecture it is true that (ii) does not imply (i) in all dimensions
> $d\geq4$, but we have not produced such examples in other dimensions than
> $4$ and $6$.

The Hilbert space is complex and has dimension $d$. The encoding indexes its
orthonormal bases by `Fin d`, relabelling the source's indices $1,\ldots,d$ as
$0,\ldots,d-1$. The projector images are the complex spans of the selected
basis vectors. Complete incompatibility includes empty index sets; condition
(ii) quantifies only over nonempty proper index sets.

## Verified locator

- DOI: https://doi.org/10.1063/5.0110267
- URL: https://arxiv.org/abs/2207.07451v1
- The arXiv source is `COINC_preprint_20220708.tex`; the projector definitions
  are in §3, Definition 4 is labelled `def:COINC`, and Proposition 7 is labelled
  `prop:incompatibilities`. The conjecture immediately follows that proposition
  in §5. The journal text has not been checked for preservation of this sentence.
