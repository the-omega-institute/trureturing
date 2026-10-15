---
bibkey: shirokov2012entropycontinuity
authors: M. E. Shirokov
year: 2012
title: "On a conjectured property of the von Neumann entropy valid in the commutative case"
doi: null
url: https://arxiv.org/abs/1201.1093v1
claim: "Entropy continuity on a closed convex family is conjectured to imply an all-temperature Hamiltonian energy bound and a common continuous bounded relative entropy reference."
strata_touched:
  - D5/S3/Quantum/Analysis/OrliczCommonEnergy
license: citation-only
triage: anchor
---

# Entropy continuity and the scalar Orlicz sufficient condition

Shirokov, arXiv:1201.1093v1, Section 3, Conjectures 1 and 2, asks about arbitrary
trace-norm closed convex families of quantum states with finite continuous von
Neumann entropy. Conjecture 1 asks for containment in an energy ball of a positive
Hamiltonian with finite partition function at every positive inverse temperature.
Conjecture 2 asks for a single state whose relative entropy is continuous and
bounded on the family. Neither conjecture assumes commutation of the states.

The related equivalence between continuous logarithmic reference energy and an
all-temperature energy bound is in Shirokov, *Entropic characteristics of subsets
of states*, arXiv:quant-ph/0510073v2, Proposition 4. This is a source for the
mathematical objective, not a claim that the scalar theorem below is stated in
either paper.

For a positive normalized reference sequence s and nonnegative normalized masses
d(x,n), the module uses the actual functions

$$
\Phi_p(t)=t(\log\max(1,t))^p,\qquad
\Psi_p(u)=\sup_{t\ge0}\{ut-\Phi_p(t)\}.
$$

A finite uniform extended Phi moment and finiteness of the actual extended dual
series at every positive scale imply uniform tails of (-log s(n))*d(x,n).
One common monotone natural weight, tending to infinity, preserves these tails
with arbitrarily small additive energy cost. For coordinatewise continuous d on
any topological space, the resulting scalar energy is finite and continuous,
and its Boltzmann series is summable at every positive inverse temperature.
The scalar implication uses p>0; nonvacuous faithful infinite-reference
applications of the every-scale condition use p>1.

This conditional sufficient criterion has stronger premises than entropy
continuity. No universal implication from the original entropy premise to a
fixed logarithmic-power moment is claimed. The spectral, noncommuting trace,
self-adjoint domain and actual heat-trace joins are separate mathematical
obligations. The scalar theorem does not resolve either original conjecture or
establish historical originality.
