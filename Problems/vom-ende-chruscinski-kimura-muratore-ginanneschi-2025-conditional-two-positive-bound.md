---
slug: vom-ende-chruscinski-kimura-muratore-ginanneschi-2025-conditional-two-positive-bound
bibkey: vomende2025twopositivebound
doi: 10.1016/j.laa.2025.10.022
url: https://arxiv.org/abs/2506.02145v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.result
---

# Spectral bound for conditionally 2-positive maps

## Problem

F. vom Ende, D. Chruściński, G. Kimura and P. Muratore-Ginanneschi,
*Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*,
arXiv:2506.02145v1, §3 “Outlook”, page 11, question (10), asks:

> Hence one may wonder whether all (generators of) completely positive maps, resp. 2-positive maps satisfy

$$
\mathrm{tr}(L)\le d\min\Re\sigma(L)+(d^2-d)\max\Re\sigma(L).
$$

> A map $L$ is called conditionally 2-positive if $e^{tL}$ is 2-positive for all $t\ge0$.

> With this, (10) becomes really a conjecture about the spectrum of arbitrary conditionally 2-positive maps.

VCKM-10 quantifies every integer $d\ge1$ and every complex-linear
endomorphism $L$ of $\mathbb C^{d\times d}$ satisfying this definition.
There is no trace-preservation assumption. The trace is the superoperator
trace; the spectrum is the set of roots of the characteristic polynomial.
The Lean claim also asserts that the superoperator trace is real.

## Motivation

This Tier-1 external named question is preregistered in
[#13633](https://github.com/the-omega-institute/trureturing/issues/13633).
`ConditionalTwoPositiveSpectralBound.result : claim` proves VCKM-10.
Its admission basis is `open-problem-resolution (#13633; Proved)`.

## Gap

The preregistration quotes arXiv v1 and reports no settlement in its bounded
literature search. The codex-cli search producer reports that
arXiv:2510.19657v3, 2603.11204v1, 2605.14644v1 and the later author paper
arXiv:2508.21348v2 do not settle this unrestricted assertion. These are
seat-reported literature readings, not an exhaustive priority claim.
The journal text is unverified. The source's Theorem 1 is already proved in
the literature and assumes trace preservation; it is a formalized
prerequisite, not a new mathematical result.

## Route

For a 2-positive map $T$, use $T_\varepsilon=T+\varepsilon\,\mathrm{tr}(\cdot)I$
with $\varepsilon>0$. Compact Collatz minimization and strict residual
lowering construct a positive-definite density $\rho$ with
$T_\varepsilon\rho=c\rho$ and $c>0$. The faithful positive-power estimate
proves that $c$ is the maximal real eigenvalue. Congruence by the square root
of $\rho$, followed by division by $c$, gives a unital 2-positive map.
Its Hilbert–Schmidt adjoint is 2-positive and trace preserving, so the
formalized Theorem 1 applies. Similarity and rescaling transport its bound
to $T_\varepsilon$. Continuity of characteristic-polynomial roots and
spectral extrema gives the bound for $T$ as $\varepsilon\to0$.
For conditionally 2-positive $L$, apply this result to $e^{tL}$ and use the
operator-exponential difference quotient as $t\downarrow0$.

## Falsifier

The literal conditional-positivity predicate, matrix dimension, exponential,
trace and spectral extrema must match the source. A failed positivity
transport, eigenmatrix construction, eigenvalue bound or limiting step
would prevent the asserted Lean proof. The public result has no additional
hypothesis beyond the quantified source claim.

## Evidence

The four Lean modules are under `D5/S3/Quantum/QuantumChannels/`:
`TwoPositiveTransitionTrace`, `TracePreservingEigenvalueBound`,
`FaithfulPerronRegularization` and `ConditionalTwoPositiveSpectralBound`.
Their Blueprint Scribes mirror the public declarations.
`TracePreservingEigenvalueBound.theorem1_general` has `FromLiterature`
provenance. The settling `result` has `OpenProblemResolutionClaim(Proved)`.
The axiom closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`. No atom or coverage is used.
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

- **Proved:** VCKM-10 for every conditionally 2-positive map, including
  reality of its superoperator trace, by `ConditionalTwoPositiveSpectralBound.result`.
  The bound for every 2-positive $T$ is the private live theorem
  `ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound`.
  The source's stated inclusions place completely positive maps and
  generators of completely positive semigroups inside the conditional
  class; the proved universal bound applies whenever that predicate holds.
  Separate public inclusion theorems are not supplied here.
- **Proved, formalized literature:** the source's Theorem 1 for every
  2-positive trace-preserving map, by
  `TracePreservingEigenvalueBound.theorem1_general`; this is not new.
- **Proved:** regularization supplies a faithful Perron eigenmatrix without
  trace preservation, by `FaithfulPerronRegularization.strict_positive_perron_eigenmatrix`
  and `regularized_perron_certificate`. The private
  `ConditionalTwoPositiveSpectralBound.unital_similarity_certificate`
  transports the trace-preserving bound. Faithful power control supplies
  the maximal-real-eigenvalue field consumed in that transport. The
  regularization and semigroup limits give the full conditional class.
- **Open:** the source's other question, a positive trace-preserving map
  violating Theorem 1 for $d\ge3$, is not addressed.
- **Proved in the cited literature:** Remark 1(iii), equation (5) and
  Example 2 show that the coefficient $d$ cannot be increased even for
  completely positive trace-preserving maps. Their maximal real eigenvalue
  is $1$, so this coefficient optimality also constrains the larger class
  of (10). The explicit sharpness family is not formalized here.
  **Open:** attainment and equality classification beyond the source's
  subclasses; this delivery proves no additional tightness statement.
- **Proved consequence:** the missing trace-preservation hypothesis in
  (10) does not obstruct its spectral bound. Source results with independent
  proofs retain their hypotheses and conclusions; uses of VCKM-10 within
  this quantified class now have the asserted bound. No full dependency
  audit of the source or resolution of its remaining positive-map question
  is claimed.

## ASSUMED-UNVERIFIED

The journal version's retention of the question is unverified because its
text has not been read. Later-paper literature conclusions are
seat-reported and bounded to the cited scope. The source's inclusions and
sharpness example are literature facts rather than additional Lean
corollaries in this delivery. Publication priority and exhaustive novelty
are not asserted.
