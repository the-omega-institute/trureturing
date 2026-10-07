---
bibkey: belkinallenclark2025secondmoments
authors: Daniel Belkin, James Allen, Bryan K. Clark
year: 2025
title: "Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits"
doi: null
url: https://arxiv.org/abs/2510.23726v2
claim: "Like the brickwork, this architecture can be shown to have a PSD vectorization if the depth is odd. It is unclear if the vectorization is PSD at even depths."
strata_touched:
  - D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl
  - D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation
license: citation-only
triage: anchor
---

# Second moments of random quantum circuits

## Verified locator

Source: https://arxiv.org/abs/2510.23726v2
The locators below use the v2 PDF: Section 2.1 on page 3, Section 5.2 on
page 12, and the PSD-circuits appendix (Appendix A.8) on pages 22–23.
This arXiv-only citation has no DOI locator.

Section 2.1 defines

$$
\Phi_\varepsilon(\rho)=\mathbb{E}_{U\sim\varepsilon}
[(U^\dagger\otimes U^\dagger)\rho(U\otimes U)],\qquad
\operatorname{vec}(\Phi_\varepsilon)=\mathbb{E}_{U\sim\varepsilon}
[U^*\otimes U^*\otimes U\otimes U].
$$

Here the star in the four-factor expectation is entrywise conjugation.
The column-first vectorization of a matrix X has entry X(row, column)
at index (column, row).

Section 2.3 (page 3) introduces the normalized permutation basis:

$$
|\sigma\rangle=\frac{1}{\sqrt{q}^{\,t}}
\sum_{\vec{i}\in\{1,\ldots,q\}^{t}}
|\vec{i}\rangle\otimes|\sigma(\vec{i})\rangle.
$$

> For $t = 2$ the only permutations are identity and swap, so the dimension of the local commutant is always $2$.

For two replicas this normalization is $q^{-1}$. The Haar moment is the
orthogonal projection onto the identity/swap span; this is the
single-gate projection used in Appendix A.8. The Gram overlaps of the
one-site vectors are one for equal permutations and $q^{-1}$ for distinct
permutations. The two-site local rule is the corresponding projection,
with mixed-vector coefficient $q/(q^2+1)$.

Section 5.2 (page 12) defines complete layers:

> Suppose we draw a random two-sided matching of the sites, then apply a layer of Haar-random 2-site gates to those pairs in parallel. In other words, we sample a random complete layer, i.e. a random set of $\frac{N}{2}$ gates such that each site is acted on by exactly one gate. This is the **parallel complete-graph** (PCG) architecture.

It then defines PB and poses the question:

> Suppose we draw layers as in the parallel complete-graph architecture, except that we require each adjacent pair of layers to form a connected block. This guarantees, for example, that we never “waste” a gate by repeating a gate from the previous layer. Avoiding this kind of waste increases the speed of scrambling. This architecture is similar to applying a single period of 1D brickwork to a random permutation of the sites, so I'll call it the **permuted brickwork** (PB). Like the brickwork, this architecture can be shown to have a PSD vectorization if the depth is odd. It is unclear if the vectorization is PSD at even depths.

For four sites the complete matchings are {(0,1),(2,3)}, {(0,2),(1,3)}
and {(0,3),(1,2)}. The union of a repeated matching has two components;
the union of any distinct two is a four-cycle. Thus the connected-block
condition is exactly that neighbouring matchings differ. The layer words
are uniform among those satisfying this condition; gates on each pair
are independent and have normalized Haar law on U(q²).

Appendix A.8 (page 23) conditions an odd-depth PB circuit on its middle
matching. Its two remaining halves are conditionally independent and
related by inversion, so the moment is an average of A† P A with P the
middle-layer projection. An even number of layers has a middle interface
between two distinct matching choices; this proof supplies no such
single middle projection. Section 2.2 (page 3) states the PSD hypothesis
of the optimal-experiment theorem and the remedy:

> Furthermore, given a locally invariant ensemble $\mathcal{E}$, one may define an ensemble $\mathcal{E}'$ with a PSD vectorization by sampling $U V^\dagger$, with $U,V$ drawn i.i.d. from $\mathcal{E}$.
