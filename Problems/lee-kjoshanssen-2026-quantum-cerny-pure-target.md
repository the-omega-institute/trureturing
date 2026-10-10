---
slug: lee-kjoshanssen-2026-quantum-cerny-pure-target
bibkey: lee2026quantumcerny
doi: 10.48550/arXiv.2609.40154
url: https://arxiv.org/abs/2609.40154v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result
---

# Pure-target quantum Černý complexity

## Problem

Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen, arXiv:2609.40154v1,
§6 item 5:

> Does a general quadratic-type saving qc_pure(w) ≤ O(√|w|) hold,
> i.e. a pure-target analogue of Theorem 2.4?

An instance consists of two quantum channels on d by d density matrices
and a start state. Letters act from left to right. The reachable set contains
the images of the start state under all binary words. A word synchronizes
when its channel is constant on this set. The complexity qc_pure(w) is the
least dimension of an instance in which w is the unique shortest
synchronizing word and its common output is pure.

The precise proposed uniform bound is the existence of a real constant C
and a natural threshold m₀ such that qc_pure(w) ≤ C√|w| for every binary
word with |w| ≥ m₀.

## Motivation

A pure common output imposes a support constraint beyond ordinary
synchronization. Constant words expose how many distinct support levels
can disappear before this output is reached.

## Gap

Tier 1. Version v1 retains item 5 as a question. Title, identifier and
author queries, together with MathDB and formal-conjectures checks,
found no settlement in the checked scope. Citation indexes were partly
inaccessible. This is a scoped absence of a located settlement, without
an exhaustive priority claim.

Bhat, Hillier, Mallick and Vijaya Kumar, arXiv:1812.08123, Theorem 3.12,
assume constancy on the whole state space. Constancy on a reachable set
is a different hypothesis and requires its own argument.

## Route

For each m, use dimension m+1, the initial projector onto e_m, an identity
channel for letter one, and Kraus operators
K_j = |e_{max(j−1,0)}⟩⟨e_j| for letter zero. They satisfy
Σ_j K_j†K_j = I. A word with z zeros sends the basis projector at j to
the basis projector at max(j−z,0). Its channel is constant on the reachable
basis projectors exactly when z ≥ m. Among words of length at most m,
only 0^m has this property. The common output is the projector at e₀.

For the lower bound, positivity supplies subspaces of vectors whose
rank-one positive matrices reach the line of the pure output after j
zero steps. These subspaces increase with j. Equality at one pair of
successive levels forces equality at every later level. For m > 0, non-synchronization
at m−1 and synchronization at m force m strict increases, beginning with
a nonzero subspace. For m = 0, existence of a density requires dimension
at least one. Thus any realization has dimension at least m+1.

## Falsifier

The argument requires complete positivity and trace preservation for the
constructed channels, a pure common output, and synchronization on the
actual reachable set. The lower bound must apply to every admissible
instance and must derive the fixed-output property from reachable-set
invariance. An empty dimension set cannot establish a complexity lower
bound under the natural-number infimum convention.

## Evidence

`D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result`
has the closed Lean type `¬ claim`. The theorem
`constant_word_complexity` gives qc_pure(0^m) = m+1 for every natural m.
`constant_word_realization` establishes that the defining dimension set is
nonempty, including at m = 0. `pure_constant_word_dimension` applies to
every instance over the canonical completely positive trace-preserving
channel interface.

The dimension proof uses positive linear functionals, their GNS nullspaces,
rank-one decompositions of positive matrices and finite-dimensional
subspace growth. It assumes no Kraus representation of the abstract zero
channel. Kraus operators are used for the explicit realization.
The axiom closure of `result` is `propext`, `Classical.choice`, `Quot.sound`.
No new axiom, `sorry`, `native_decide` or floating-point evaluation occurs.

## Triage

- [proved: D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result]
  The general pure-target square-root saving is false. For any proposed
  real constant and length threshold, a sufficiently long constant word
  violates the proposed bound.
- [proved: D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.constant_word_complexity]
  The constant-word family has exact complexity m+1. Its construction
  shows sharpness of the dimension obstruction at every natural length,
  rather than failure only at a single finite word.
- [proved: D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.pure_constant_word_dimension]
  The obstruction comes from a pure fixed output and positivity. A plateau
  in the subspaces of vectors whose rank-one matrices reach the output
  line cannot be followed by a later increase. When m > 0, failure at
  step m−1 therefore forces all m increases. At m = 0, existence of a
  density requires dimension at least one. The other letter's channel
  can be arbitrary; constancy on the whole state space is unnecessary.
- [open] Determine which additional restrictions on words permit a
  square-root bound with pure common output. Excluding constant words
  removes this particular family without establishing a bound on the
  remaining words.
- [open] Theorem 2.4 concerns the ordinary target setting and requires
  separate formal verification. This pure-target obstruction does not
  refute that distinct assertion or settle the other questions in §6.

## ASSUMED-UNVERIFIED

Only arXiv v1 and the stated scoped literature checks underpin the
literature status. The inaccessible portions of citation indexes remain
unchecked. No exhaustive priority determination or later-version
comparison is asserted. The scope of arXiv:1812.08123 Theorem 3.12 is
constancy on the whole state space, rather than only a reachable set.
