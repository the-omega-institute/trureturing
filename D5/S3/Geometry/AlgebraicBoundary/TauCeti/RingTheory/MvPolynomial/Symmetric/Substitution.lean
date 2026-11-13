/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
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

## Main declarations

* `MvPolynomial.IsSymmetric.exists_aeval_esymm`: the fundamental theorem of symmetric polynomials,
  unbundled: a symmetric polynomial is a polynomial in the elementary symmetric polynomials.
* `MvPolynomial.IsSymmetric.bind₁_aeval_X`: uniform univariate substitution preserves
  symmetry.
* `MvPolynomial.IsSymmetric.exists_aeval_esymm_eq_bind₁_aeval_X`: the substituted
  polynomial is a polynomial in the elementary symmetric polynomials.
-/

public section

open Polynomial

namespace TauCeti

/-- Substituting the same univariate polynomial into every variable of a symmetric multivariate
polynomial preserves symmetry. -/
theorem _root_.MvPolynomial.IsSymmetric.bind₁_aeval_X
    {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}
    (hp : p.IsSymmetric) (q : R[X]) :
    (MvPolynomial.bind₁ (fun i => Polynomial.aeval (MvPolynomial.X i) q) p).IsSymmetric := by
  intro e
  calc
    MvPolynomial.rename e
        (MvPolynomial.bind₁ (fun i => Polynomial.aeval (MvPolynomial.X i) q) p) =
        MvPolynomial.bind₁
          (fun i => MvPolynomial.rename e (Polynomial.aeval (MvPolynomial.X i) q)) p := by
      rw [MvPolynomial.rename_bind₁]
    _ = MvPolynomial.bind₁
          ((fun i => Polynomial.aeval (MvPolynomial.X i) q) ∘ e) p := by
      apply congrArg (fun f => MvPolynomial.bind₁ f p)
      funext i
      calc
        MvPolynomial.rename e (Polynomial.aeval (MvPolynomial.X i) q) =
            Polynomial.aeval (MvPolynomial.rename e (MvPolynomial.X i)) q :=
          (Polynomial.aeval_algHom_apply (MvPolynomial.rename e) (MvPolynomial.X i) q).symm
        _ = Polynomial.aeval (MvPolynomial.X (e i)) q := by rw [MvPolynomial.rename_X]
    _ = MvPolynomial.bind₁ (fun i => Polynomial.aeval (MvPolynomial.X i) q)
          (MvPolynomial.rename e p) := by
      rw [MvPolynomial.bind₁_rename]
    _ = MvPolynomial.bind₁ (fun i => Polynomial.aeval (MvPolynomial.X i) q) p := by
      rw [hp e]

/-- **The fundamental theorem of symmetric polynomials**, unbundled: a symmetric polynomial in `n`
variables over a commutative ring is a polynomial in the first `n` elementary symmetric
polynomials. -/
theorem _root_.MvPolynomial.IsSymmetric.exists_aeval_esymm
    {R : Type*} [CommRing R] {n : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : p.IsSymmetric) :
    ∃ W : MvPolynomial (Fin n) R,
      MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) R ((j : ℕ) + 1)) W = p := by
  obtain ⟨W, hW⟩ := (MvPolynomial.esymmAlgHom_fin_bijective R n).surjective
    (⟨p, hp⟩ : MvPolynomial.symmetricSubalgebra (Fin n) R)
  refine ⟨W, ?_⟩
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact congrArg Subtype.val hW

/-- Over a commutative ring, uniformly substituting a univariate polynomial into a symmetric
polynomial in `n` variables yields a polynomial in the first `n` elementary symmetric
polynomials: the substituted polynomial is symmetric by
`MvPolynomial.IsSymmetric.bind₁_aeval_X`, so the fundamental theorem
(`MvPolynomial.IsSymmetric.exists_aeval_esymm`) applies to it. -/
theorem _root_.MvPolynomial.IsSymmetric.exists_aeval_esymm_eq_bind₁_aeval_X
    {R : Type*} [CommRing R] {n : ℕ}
    {p : MvPolynomial (Fin n) R} (hp : p.IsSymmetric) (q : R[X]) :
    ∃ W : MvPolynomial (Fin n) R,
      MvPolynomial.aeval
          (fun j : Fin n => MvPolynomial.esymm (Fin n) R ((j : ℕ) + 1)) W =
        MvPolynomial.bind₁ (fun i => Polynomial.aeval (MvPolynomial.X i) q) p :=
  (hp.bind₁_aeval_X q).exists_aeval_esymm

end TauCeti
