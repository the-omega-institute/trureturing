/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/MvPolynomial/Rename
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/MvPolynomial/Rename
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/MvPolynomial/Rename.lean.
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

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Renaming variables, and discarding the ones outside the range

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` is a
ring equivalence. Mathlib's `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` are deliberately not instances, so this file registers them
for `MvPolynomial.renameEquiv`. This lets semilinear equivalences over variable renaming be used
and inverted without requiring downstream local instances.

Along an injective renaming `f : σ → τ`, Mathlib's `MvPolynomial.killCompl` sets the variables
outside the range of `f` to zero. When exactly one variable `X a` is discarded, the polynomials
it kills are exactly the multiples of `X a`.

## Main definitions

* `TauCeti.renameRingHomInvPair`: variable renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.renameRingHomInvPairSymm`: the same inverse pair in the reverse direction.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f) {a : τ}

end MvPolynomial

namespace Polynomial

/-- Renaming the parameters of a polynomial family `P : (MvPolynomial σ R)[X]` along `f` and then
specializing them at `y` is specializing `P` at `y ∘ f`. -/
theorem map_eval_map_rename {σ τ R : Type*} [CommSemiring R] (f : σ → τ)
    (P : (MvPolynomial σ R)[X]) (y : τ → R) :
    (P.map (MvPolynomial.rename (R := R) f).toRingHom).map (MvPolynomial.eval y) =
      P.map (MvPolynomial.eval (y ∘ f)) := by
  rw [Polynomial.map_map]
  congr 1
  ext <;> simp

end Polynomial

namespace TauCeti

variable {σ τ : Type*} (R : Type*) [CommSemiring R]

end TauCeti
