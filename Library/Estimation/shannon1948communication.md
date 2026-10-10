---
bibkey: shannon1948communication
authors: Claude E. Shannon
year: 1948
title: A Mathematical Theory of Communication
doi: null
url: https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf
claim: "The corrected reprint defines finite entropy, joint entropy and conditional entropy, with joint entropy at most the sum of marginal entropies and equality exactly for independence."
strata_touched: []
license: citation-only
triage: anchor
---

# Finite entropy and the meaning of relative entropy in the reprint

The primary text is the [corrected reprint](https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf)
of *A Mathematical Theory of Communication*, Bell System Technical Journal
27, 379–423 and 623–656. Its introductory discussion of logarithm bases
gives bits for base two. Section 6, Theorem 2 and the properties following
it, printed pp. 11–12, define finite entropy and conditional entropy and give

$$
H(X,Y)=H(X)+H(Y\mid X),\qquad H(X,Y)\le H(X)+H(Y).
$$

The equality condition in the second relation is independence. Zero-mass
conditional events are excluded from division; their weighted entropy
contribution is zero, using the continuous convention $0\log 0=0$.

Section 7, printed p. 14, calls the ratio of a source's entropy to its
maximum possible entropy on the same alphabet its “relative entropy.”
This normalized entropy ratio is distinct from the modern divergence
$D(p\Vert q)=\sum p\log(p/q)$. The latter definition and its finite-law
inequality in the consumer have a separate source and proof.

The [foundational pyramid reference, §九](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)
uses the finite entropy and chain rule on a single five-mode law.
Its support-inclusive maximum-entropy completion and continuing-reply
logarithmic prediction loss are proved there. Shannon's source supplies
neither native FIB guards nor acquisition of an unknown law.
