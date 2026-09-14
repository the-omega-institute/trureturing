---
bibkey: klukowski2024congruence
authors: Adam Klukowski
year: 2024
title: Congruence subgroup property for nilpotent groups and subsurface subgroups of Mapping Class Groups
arxiv: 2411.06867v2
claim: Finite characteristic quotients define congruence subgroups; the paper proves congruence separability for solvable subgroups and formulates a curve-orbit congruence-control conjecture.
strata_touched:
  - D5/S3/Observer/Dynamics/SurfaceTwistCongruence
license: citation-only
triage: anchor
---

# Surface congruence and finite nonabelian observations

Primary source read: https://arxiv.org/html/2411.06867v2

## Exact scope

Definition 3 uses a finite characteristic quotient of a group G and the induced
map on Out(G) to define congruence subgroups. Corollary 7 already proves
congruence separability of solvable subgroups of a mapping class group.
Theorem 8 controls inclusion of subsurface subgroups. Corollaries 10 and 11
handle stabilizers of sufficiently large multicurves and their intersections
with principal congruence kernels.

Conjecture 13 asks: for any finite-index subgroup Gamma of Mcg(Sigma) and any
simple closed curve alpha, does a congruence subgroup Delta exist with
Delta.alpha contained in Gamma.alpha? The current bounded search did not find
a resolution of this general statement. This does not establish exhaustive
priority or rule out unpublished work. Genus at least three is the unsolved
CSP horizon in Conjecture 1; known low-genus CSP is not a new target.

Lemma 14 is a known composition lemma. It requires both the restricted CSP
and a congruence condition for all finite-index subgroups containing the
selected subgroup. Detecting all powers of one separating twist does not
supply the second premise or prove Conjecture 13.

## Relation to the explicit construction

The new source uses the actual genus-(extra+2) presentation and constructs a
finite fully invariant quotient as the image of evaluation at all maps to a
dihedral group of order 8m. It proves the exact outer period m of the chosen
partial-conjugation automorphism. Its lower bound compares two generator
images under one common conjugation; its upper bound works for every map to
the target. This note does not attribute the particular 8m target or the
matching explicit formula to a numbered result of Klukowski.

The qualitative consequence for the cyclic twist subgroup is classical and
already covered by broader known congruence results. It is not an external
open problem solved here. The proof source is a candidate construction, not
a claim of mathematical first discovery or repository admission.

## Other primary context

- Wilton and Sisto, *The congruence subgroup property for mapping class groups
  and the residual finiteness of hyperbolic groups*, arXiv:2410.00556.
  https://arxiv.org/abs/2410.00556 . The general CSP conclusion assumes residual
  finiteness of every hyperbolic group; that premise is not available here.
- Boggi, *A congruence subgroup property for symmetric mapping class groups*,
  arXiv:2408.12486. https://arxiv.org/abs/2408.12486 . Its centralizer result
  assumes quotient-surface genus at most two. It is not an unconditional
  solution for all higher-genus mapping class groups.

## Bounded source and implementation audit

2026-09-14: read the sources above and searched separating-twist/dihedral and
mapping-class CSP combinations. Repository searches for SeparatingTwist and
Klukowski returned no matching owner. Generic surface results mainly concerned
engineering surfaces. Read the merged #7614 disposition: its nine previous
candidate Lean modules were withdrawn; none is imported here. No claim that
all open PRs or all external libraries were searched is made.

The only proof upstream is mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Read the actual
`GroupTheory/PresentedGroup.lean` and `SpecificGroups/Dihedral.lean` APIs.
No existing exact canonical-quotient/outer-order theorem was located in this
bounded search. Finite diagnostics check group operations, the relator,
repeated twists and simultaneous conjugacy; they do not certify Lean
elaboration, whole-kernel invariance or unbounded quantifiers.

## Second-derived word orbit and the actual research boundary

The follow-up source is
`D5/S3/Observer/Dynamics/SurfaceDerivedOrbitDetector.lean`, with paired Scribe.
It reuses the original presentation and twist. For genus at least three it
chooses u=[[a1,a2],[b1,b3]], which lies in the second derived subgroup. The
new explicit seven-dimensional representation family reads tau^n(u) as
I-(n+t)E17. Evaluating at t=-p separates two time indices modulo m even under
conjugacy. The quotient used by the Lean candidate is the image of evaluation
at all GL7(Z/m)-valued homomorphisms, so its kernel is fully invariant.
For this larger target the modular condition is necessary, with an exact
finite-window consequence. No converse for all times is claimed there.

The existing theory now separately proves the class-six threshold and the
exact period for the smaller all-UT7 evaluation quotient. The lower-central
filtration argument and this smaller quotient have not been formalized in
the new Lean source. The matrix witness is valid at even and composite
moduli; no division by two or by a factorial is used. A single representation
kernel is never silently substituted for the fully invariant kernel.

Section 3 of Klukowski gives the Andreadakis-Johnson background for an
automorphism acting trivially on G/gamma_3 and its higher commutator defects.
The precise chosen word and its explicit matrix coefficient are not attributed
to a theorem in that paper. No source was found for this exact formula in the
bounded separating-twist/unitriangular searches. This is not a priority claim.
The qualitative existence of finite detecting quotients and standard
lower-central commutator calculus are classical.

A topological limitation is explicit in the appended theory: a nontrivial
second-derived surface-group word cannot represent an essential simple closed
curve. Nonseparating curves have nonzero homology; a separating curve has a
nontrivial image under a relator-compatible integral Heisenberg representation,
which kills the second derived subgroup. Thus the chosen u cannot replace the
simple curve alpha in Conjecture 13. The full stabilizer-coset inclusion
C subset Gamma Stab(alpha) is still unproved by this construction.

The earlier low-genus shorthand has a specific boundary: Klukowski's
introduction distinguishes punctured genus one from the unpunctured torus.
The latter has fundamental group Z^2 and its usual SL2(Z) action lacks CSP.
No unqualified genus-one CSP assertion should be inferred from this note.

## Additional verified primary references

- Thomas Church and Aaron Pixton, *Separating twists and the Magnus
  representation of the Torelli group*, Geometriae Dedicata 155 (2011),
  177-190. https://arxiv.org/abs/0804.3633 . The arXiv record was revised on
  January 13, 2011. Its abstract supplies the Magnus/separating-twist context.
  It is not cited as a source for the exact UT7 formula above.
- Taylor McNeill, *A new filtration of the Magnus kernel of the Torelli group*,
  arXiv:1308.3686. https://arxiv.org/abs/1308.3686 . This work uses a surface
  with one boundary and a free fundamental group. Its Magnus-kernel examples
  are not silently transferred to the present closed-surface carrier.
- Thomas Koberda and Mark Pengitore, *Linearity criteria for automorphism
  groups of malabelian groups*, Mathematische Annalen 395, article 100 (2026),
  published July 6, 2026. DOI 10.1007/s00208-026-03530-5.
  https://link.springer.com/article/10.1007/s00208-026-03530-5
  https://arxiv.org/html/2510.14571v2
  The publisher page and arXiv introduction were read on September 14, 2026.
  Its linearity criterion uses invariant finite quotients built from products
  of extension-bounded nonabelian finite simple groups of Lie type, with the
  stated finite-index qualifications and bounds over whole word balls.
  A single-word solvable UT7 detector does not satisfy those hypotheses.
  In that paper, malabelian is a centralizer condition; it is distinct from
  metabelian, the condition that the second derived subgroup is trivial.

The new candidate and the old #7710 source remain uncompiled in this work
environment. Exact matrix diagnostics, source review and Git object matching
are not Lean kernel verification or independent admission review. The
class-six threshold and simple-curve exclusion are ordinary proofs in the
theory appendix. No external open conjecture is recorded as solved.
