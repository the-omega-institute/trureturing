/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/MvPolynomial/Equiv
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/MvPolynomial/Equiv
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/MvPolynomial/Equiv.lean.
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

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Data.Finsupp.Fin

/-!
# Singling out an arbitrary variable of a polynomial ring in `n + 1` variables

Mathlib's `MvPolynomial.finSuccEquiv` identifies `R[X₀, …, Xₙ]` with the polynomial ring in the
variable `X₀` over `R[X₁, …, Xₙ]`. This file does the same with an arbitrary variable `Xₚ`
singled out: the remaining variables are indexed by `Fin n` through `p.succAbove`, as in the
equivalence `finSuccEquiv' p : Fin (n + 1) ≃ Option (Fin n)`.

This is the form in which a polynomial ring acquires one new variable in the middle of its
list, as happens to the coefficient ring of a grid complex when a grid diagram is stabilized.

## Main definitions

* `MvPolynomial.finSuccEquiv'`: the `R`-algebra isomorphism
  `R[X₀, …, Xₙ] ≃ R[X_{p.succAbove 0}, …, X_{p.succAbove (n-1)}][Xₚ]`.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace MvPolynomial

variable (R : Type*) [CommSemiring R] {n : ℕ}

/-- The `R`-algebra isomorphism between polynomials in the variables `Fin (n + 1)` and
polynomials in the variable `X p` over the polynomials in the other variables, which are indexed
by `Fin n` through `p.succAbove`. -/
noncomputable def finSuccEquiv' (p : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' p)).trans (optionEquivLeft R (Fin n))

variable {R}

/-- The singled-out variable becomes the polynomial variable. -/
@[simp]
theorem finSuccEquiv'_X_self (p : Fin (n + 1)) : finSuccEquiv' R p (X p) = Polynomial.X := by
  simp [finSuccEquiv', optionEquivLeft_X_none]

/-- A variable other than the singled-out one becomes a constant. -/
@[simp]
theorem finSuccEquiv'_X_succAbove (p : Fin (n + 1)) (i : Fin n) :
    finSuccEquiv' R p (X (p.succAbove i)) = Polynomial.C (X i) := by
  simp [finSuccEquiv', optionEquivLeft_X_some]

/-- Constants stay constant. -/
@[simp]
theorem finSuccEquiv'_C (p : Fin (n + 1)) (r : R) :
    finSuccEquiv' R p (C r) = Polynomial.C (C r) :=
  (finSuccEquiv' R p).commutes r

/-- Singling out the variable `X 0` is `MvPolynomial.finSuccEquiv`. -/
theorem finSuccEquiv'_zero : finSuccEquiv' R (0 : Fin (n + 1)) = finSuccEquiv R n := by
  rw [finSuccEquiv', finSuccEquiv, _root_.finSuccEquiv'_zero]

section Map

variable {S : Type*} [CommSemiring S]

/-- Singling out a variable commutes with mapping the coefficients along `φ`. -/
theorem finSuccEquiv'_map (φ : R →+* S) (p : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv' S p (map φ f) = (finSuccEquiv' R p f).map (map φ) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp only [map_add, Polynomial.map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, Polynomial.map_mul, hf, map_X]
    congr 1
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Specializing the variables other than `X p` along `φ` at the point `s`, and then evaluating
the polynomial variable at `y`, is evaluating along `φ` at the point obtained by inserting `y`
into `s` at position `p`. -/
theorem polynomial_eval_map_finSuccEquiv' (φ : R →+* S) (p : Fin (n + 1)) (s : Fin n → S)
    (y : S) (f : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv' R p f).map (eval₂Hom φ s)).eval y = eval₂ φ (Fin.insertNth p y s) f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp only [map_add, Polynomial.map_add, Polynomial.eval_add, hf, hg, eval₂_add]
  | mul_X f i hf =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hf, eval₂_mul, eval₂_X]
    congr 1
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Specializing the variables `X 1, …, X n` along `φ` at the point `s`, and then evaluating the
polynomial variable at `y`, is evaluating along `φ` at the point `Fin.cons y s`. -/
theorem polynomial_eval_map_finSuccEquiv (φ : R →+* S) (s : Fin n → S) (y : S)
    (f : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv R n f).map (eval₂Hom φ s)).eval y = eval₂ φ (Fin.cons y s) f := by
  simpa only [finSuccEquiv'_zero, Fin.insertNth_zero'] using
    polynomial_eval_map_finSuccEquiv' φ 0 s y f

end Map

section Last

open Finsupp

end Last

end MvPolynomial
