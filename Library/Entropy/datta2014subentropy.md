---
bibkey: datta2014subentropy
authors: Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti
year: 2014
title: "Properties of subentropy"
doi: 10.1063/1.4882935
url: https://arxiv.org/abs/1310.1312
claim: "Subentropy has a finite simple-spectrum formula with continuous extension to repeated and zero eigenvalues; Conjecture 1 asks for bipartite subadditivity."
strata_touched:
  - D5/S3/Quantum/Subentropy/SpectralFormula
  - D5/S3/Quantum/Subentropy/DensityKernel
  - D5/S3/Quantum/Subentropy/Subadditivity
  - D5/S3/Quantum/Subentropy/POVMGram
license: citation-only
triage: anchor
---

# Subentropy: spectral formula and subadditivity

## Locator

- URL: https://arxiv.org/abs/1310.1312
- DOI: 10.1063/1.4882935 — **ASSUMED-UNVERIFIED**; supplied citation, not checked against an original arXiv abstract page or publisher record.
- Spectral formula locator supplied by the mathematical route: arXiv:1310.1312v1, equation (1).
- arXiv:1310.1312v1, §2.3.1, Conjecture 1:

  > Conjecture 1. Subentropy is subadditive: Q(ρAB) ≤ Q(ρA) + Q(ρB).

- arXiv:1310.1312v1, §2.5.1, Conjecture 2:

  > Conjecture 2. For a c-q state ρXB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ Hmin(X|B) = − ln pguess(X|B).

## Mathematical scope

For positive pairwise distinct probabilities $p_1,\ldots,p_N$, the cited
subentropy is

$$
Q(p)=-\sum_{i=1}^N
\frac{p_i^N\log p_i}{\prod_{j\ne i}(p_i-p_j)}.
$$

Repeated and zero eigenvalues require the continuous extension, rather than
evaluation of the quotient with a zero-denominator convention. The original
subentropy attribution is Jozsa–Robb–Wootters (1994); no independently
verified original-paper locator is asserted here.

Conjecture 1 is $Q(\rho_{AB})\le Q(\rho_A)+Q(\rho_B)$ for bipartite density
operators. It is a different assertion from strong subadditivity. The latter's
Bell-state counterexample does not refute Conjecture 1.

## Attribution boundary

The arXiv identifier, DOI, spectral formula and conjecture attribution are
supplied source information. The expanded author names, title and exact
formula/conjecture locations are **ASSUMED-UNVERIFIED** until checked against
the original source.

The determinant-integral representation, its domination estimate
and its rectangular-Gram invariance are repository derivations rather than results attributed to this note. This citation-only
note incorporates no source software.

Literature-check result: searches of the arXiv identifiers, “subentropy
subadditive”, “strong subadditivity” with subentropy, and the titles found
no answer; citation indexes were not exhaustively checked.

The finite-dimensional subadditivity result is
[Subadditivity.subentropy_subadditive](../../D5/S3/Quantum/Subentropy/Subadditivity.lean).
It applies to every bipartite density state and its actual two marginals.
The proof uses the repository's Gaussian representation and convex pinching
gap, followed by an unnormalized c-q block Gram construction. These
are repository derivations, not assertions attributed to the cited paper.

## Conditional guessing bound

The supplied locator for Conjecture 2 is arXiv:1310.1312v1, §2.5.1:

> Conjecture 2. For a c-q state ρXB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ Hmin(X|B) = − ln pguess(X|B).

For the canonical c-q record state, conditional subentropy means the record
subentropy minus the mixture subentropy. The guessing probability is the
supremum of the success probabilities over all positive semidefinite POVM
elements with the label set as outcomes and sum equal to the identity.
The stronger theorem is Q(X|B)<=1-p_guess<=-log p_guess, proved in
[POVMGram.cq_conditional_subentropy_guessing](../../D5/S3/Quantum/Subentropy/POVMGram.lean).
Its guessing probability is defined as the supremum of that precise success
set, whose nonemptiness and boundedness are proved. The conditional states
are the canonical recordState and mixtureState.

Both theorems use the determinant-integral subentropy. The frozen
SubentropyLike uniqueness identification equates every continuous invariant
family obeying the simple-spectrum formula with this value, including at
zero or repeated eigenvalues. Thus the statements apply to the paper's
continuous-extension convention.
The quotation and exact locator are supplied source information,
**ASSUMED-UNVERIFIED** against the original paper under the offline constraint.
No source-derived proof of either conjecture is asserted.
