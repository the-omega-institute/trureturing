/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Substitution in symmetric multivariate polynomials

Substituting the same univariate polynomial into every variable of a symmetric multivariate
polynomial preserves symmetry. For finitely many variables over a commutative ring, the fundamental
theorem of symmetric polynomials then expresses the substituted polynomial in the elementary
symmetric polynomials.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

open Polynomial

namespace TauCeti

end TauCeti
