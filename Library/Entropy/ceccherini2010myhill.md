---
bibkey: ceccherini2010myhill
authors: Tullio Ceccherini-Silberstein, Michel Coornaert
year: 2010
title: The Myhill property for strongly irreducible subshifts over amenable groups
doi: 10.1007/s00605-010-0256-2
url: https://arxiv.org/abs/1004.2422v2
claim: Theorem 1.1 proves the Myhill property for strongly irreducible finite-alphabet subshifts over possibly uncountable amenable groups; Lemma 4.1 supplies strict relative pattern loss and Lemma 4.6 supplies common-exterior realization.
strata_touched:
  - D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill
license: citation-only
triage: anchor
---

# Myhill on strongly irreducible subshifts

Theorem 1.1 states that, for a possibly uncountable amenable group G and
finite alphabet A, every strongly irreducible subshift X contained in
A^G has the Myhill property. A cellular automaton is a continuous
G-equivariant endomorphism of X. Preinjectivity compares complete
images of configurations with finite disagreement. No finite-type,
countability or finite-generation hypothesis is imposed.

The paper uses g*x(h)=x(g⁻¹*h), the collar F*Delta⁻¹, and finite
two-pattern gluing under disjointness of that collar from the second
support. Lemma 4.1 compares counts of globally occurring X-patterns,
not all alphabet words. Within a nonempty exterior fiber there are at
most card(X_E) completions, and at least one completion realizes the
excluded pattern. Successive exclusions consequently give a strict
relative counting factor.

Common-exterior realization follows by compactness from all finite
exterior gluing constraints. This retains a nonsymmetric witness
Delta. A direct two-set use of the separation convention must also
check the reverse separation when the chosen witness is not symmetric.
The local support letters in the Lemma 4.1 proof must be read according
to the preceding exclusion on the smaller pattern support.

The native statement uses the nontrivial maximal counting Foelner
filter for the opposite action (op e) • h=h*e. It keeps the arbitrary
index filter and right-padding limits, without replacing amenability
by an invariant-mean equivalence. The proof works on the actual
carrier subtype and derives finite memory from continuity there.
Only mathematical statements and arguments are cited; no external
Lean source is copied.

## Verified locator

DOI: https://doi.org/10.1007/s00605-010-0256-2.
Version: https://arxiv.org/abs/1004.2422v2.
Theorem 1.1, Lemmas 4.1 and 4.6, Proposition 4.2, Theorem 5.1 and
Corollary 5.2 in arXiv:1004.2422v2 give the theorem and proof components.
