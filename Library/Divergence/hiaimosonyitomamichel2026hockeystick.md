---
bibkey: hiaimosonyitomamichel2026hockeystick
authors: Fumio Hiai; Milan Mosonyi; Marco Tomamichel
year: 2026
title: Hockey stick f-divergences
url: https://arxiv.org/abs/2607.08760v1
claim: "Proposition V.1 gives the maximal positive-overlap hockey formulas and a three-label attaining reverse test; the final equality question concerns maximal hockey-stick versus maximal f-divergence."
strata_touched:
  - D5/S3/Quantum/Divergence/MaximalHockeyStickOperational
  - D5/S3/Quantum/Divergence/MaximalHockeyStickConvex
license: citation-only
triage: anchor
---

# Maximal hockey profiles and the finite-source equality question

Hiai, Mosonyi and Tomamichel, *Hockey stick f-divergences*,
arXiv:2607.08760v1, Proposition V.1, pp. 34--36, equations
(V.124)--(V.125), identify the maximal positive and negative hockey
divergences with the two trace masses minus the maximal positive common
overlap. Their proof constructs three classical labels from an attained
positive common lower bound and its two positive residuals. This is a
known result, following Matsumoto's formulation, rather than a new
conjecture solution. The final equality question on p. 62 asks when
maximal hockey-stick f-divergence equals maximal f-divergence.

The finite-matrix formalization uses all natural k and actual
density-matrix preparations on Fin k, with arbitrary nonnegative input
masses. For t>0, MaximalHockeyStickOperational proves both operational
infimum formulas using an attained PSD overlap X and the independently
indexed components X, A-X, tB-X. The same test attains both orientations.
Zero-mass components have an arbitrary coordinate state with zero weight;
empty matrix dimension uses the empty alphabet. The statements retain
singular and zero pairs and impose no trace-one or nonempty-dimension
hypothesis. The positive-threshold restriction is sufficient for every
curvature integral used here.

For S=A+B, C=normalize(S,A) and P the spectral projection of C onto
(0,1), the repository's finite-source classifier states the following.
For any real generator convex on the positive ray with actual
right-derivative curvature of full support, if the infimum of its closed
perspective cost over all finite tests is real finite, equality with its
integrated operational hockey value holds exactly when PSP commutes with
PCP. Sufficiency holds for every such convex generator as an equality
of extended values, without the full-support or finite-value hypotheses.
Necessity uses approximate finite tests with integrable nonnegative gaps,
not general-convex attainment. The atom at one belongs to the negative
branch; the scalar endpoint limits may be infinite. No infimum-integral
interchange is assumed.

Hiai, *Quantum f-divergences in von Neumann algebras II. Maximal
f-divergences*, arXiv:1807.03118v1, Theorem 4.2, Lemma 6.1 and Theorem
6.3, supplies canonical spectral and operator-convex optimality
antecedents. Matsumoto, *A new quantum version of f-divergence*, in
*Nagoya Winter Workshop 2015: Reality and Measurement in Algebraic
Quantum Theory*, pp. 229--273 (2018), is the attainment antecedent cited
by HMT. GGJ's *On the infimum of quantum effects* is separately credited
for common-support localization. None is credited with the repository's
general convex approximate-test classification. No Bayer--Teichmann
cubature theorem is consumed.

The finite/all-L1 source equivalence and the arbitrary von Neumann
algebra theorem require separate proofs. The present finite-source
classification does not assert either. Operator-convex generators are
included only under the stated curvature and finite-value conditions
for necessity. Worldwide priority of the classification remains
unresolved; source attribution and Lean verification are distinct.
