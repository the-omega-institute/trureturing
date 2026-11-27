/- GID: D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual Legendre signs and binary left inverses certify rational squareclass independence. -/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false
open scoped BigOperators Matrix

namespace D5.S3.Factorization.QuadraticIdeals.FiniteLegendreSquareclassCertificate

/-- Encode a negative Legendre sign by (1) and a positive sign by (0). -/
def signBit (a : ℤ) : ZMod 2 := if a = -1 then 1 else 0

private theorem signBit_mul {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : signBit (a * b) = signBit a + signBit b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem cast_prod_ne_zero {ι : Type*} {q : ℕ} [Fact q.Prime]
    (d : ι → ℤ) (s : Finset ι) (hd : ∀ j ∈ s, (d j : ZMod q) ≠ 0) :
    ((∏ j ∈ s, d j : ℤ) : ZMod q) ≠ 0 := by
  push_cast
  exact Finset.prod_ne_zero_iff.mpr hd

private theorem legendre_signBit_prod {ι : Type*} {q : ℕ} [Fact q.Prime]
    (d : ι → ℤ) (s : Finset ι) (hd : ∀ j ∈ s, (d j : ZMod q) ≠ 0) :
    signBit (legendreSym q (∏ j ∈ s, d j)) =
      ∑ j ∈ s, signBit (legendreSym q (d j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signBit]
  | @insert j s hj ih =>
    have hDj : (d j : ZMod q) ≠ 0 := hd j (Finset.mem_insert_self j s)
    have hDs : ∀ k ∈ s, (d k : ZMod q) ≠ 0 := fun k hk => hd k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert hj, Finset.sum_insert hj, legendreSym.mul, signBit_mul, ih hDs]
    · exact legendreSym.eq_one_or_neg_one q hDj
    · exact legendreSym.eq_one_or_neg_one q (cast_prod_ne_zero d s hDs)

variable {ι κ : Type*}

/-- The Legendre sign matrix: rows are auxiliary primes, columns discriminants. -/
def legendreMatrix (q : κ → ℕ) [∀ i, Fact (q i).Prime] (d : ι → ℤ) :
    Matrix κ ι (ZMod 2) :=
  Matrix.of fun i j => signBit (legendreSym (q i) (d j))

/-- Independent binary Legendre columns detect every nonempty rational squareclass relation. -/
theorem not_isSquare_product_of_injective [Fintype ι]
    (q : κ → ℕ) [∀ i, Fact (q i).Prime] (d : ι → ℤ)
    (hnz : ∀ i j, (d j : ZMod (q i)) ≠ 0)
    (hrank : Function.Injective (fun x : ι → ZMod 2 => legendreMatrix q d *ᵥ x))
    (s : Finset ι) (hs : s.Nonempty) : ¬IsSquare (∏ j ∈ s, (d j : ℚ)) := by
  classical
  intro hsq
  have hsqInt : IsSquare (∏ j ∈ s, d j) := by
    apply Rat.isSquare_intCast_iff.mp
    push_cast
    exact hsq
  let x : ι → ZMod 2 := fun j => if j ∈ s then 1 else 0
  have hker : legendreMatrix q d *ᵥ x = 0 := by
    funext i
    change (∑ j, legendreMatrix q d i j * x j) = 0
    have hsum : (∑ j, legendreMatrix q d i j * x j) =
        ∑ j ∈ s, signBit (legendreSym (q i) (d j)) := by
      simp only [legendreMatrix, Matrix.of_apply, x, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      simp
    rw [hsum, ←legendre_signBit_prod d s (fun j _ => hnz i j)]
    have hex : ((∏ j ∈ s, d j : ℤ) : ZMod (q i)) ≠ 0 :=
      cast_prod_ne_zero d s (fun j _ => hnz i j)
    have hmodsq : IsSquare ((∏ j ∈ s, d j : ℤ) : ZMod (q i)) :=
      hsqInt.map (Int.castRingHom (ZMod (q i)))
    rw [(legendreSym.eq_one_iff (q i) hex).mpr hmodsq]
    decide
  have hx0 : x = 0 := hrank (hker.trans (Matrix.mulVec_zero _).symm)
  obtain ⟨j, hj⟩ := hs
  have h := congrFun hx0 j
  simp [x, hj] at h

/-- Numerator times denominator gives an integer in the same rational squareclass. -/
def integralRepresentative (a : ℚ) : ℤ := a.num * a.den

private theorem integralRepresentative_cast (a : ℚ) :
    (integralRepresentative a : ℚ) = a * ((a.den : ℚ) * a.den) := by
  calc
    (integralRepresentative a : ℚ) = (a.num : ℚ) * (a.den : ℚ) := by
      simp [integralRepresentative]
    _ = ((a.num : ℚ) / (a.den : ℚ)) * ((a.den : ℚ) * a.den) := by
      field_simp
    _ = a * ((a.den : ℚ) * a.den) := by rw [Rat.num_div_den]

/-- A finite Legendre matrix for rational inputs is obtained by first
multiplying each input by the square of its denominator. -/
theorem not_isSquare_rational_product_of_injective [Fintype ι]
    (q : κ → ℕ) [∀ i, Fact (q i).Prime] (d : ι → ℚ)
    (hnz : ∀ i j, (integralRepresentative (d j) : ZMod (q i)) ≠ 0)
    (hrank : Function.Injective (fun x : ι → ZMod 2 =>
      legendreMatrix q (integralRepresentative ∘ d) *ᵥ x))
    (s : Finset ι) (hs : s.Nonempty) : ¬IsSquare (∏ j ∈ s, d j) := by
  intro hsq
  refine not_isSquare_product_of_injective q (integralRepresentative ∘ d) hnz hrank s hs ?_
  simp only [Function.comp_apply, integralRepresentative_cast, Finset.prod_mul_distrib]
  exact hsq.mul (IsSquare.mul_self _)

/-- A left inverse is a finite, checkable witness that the certificate has full column rank. -/
theorem injective_mulVec_of_left_inverse [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : Matrix κ ι (ZMod 2)) (N : Matrix ι κ (ZMod 2))
    (h : N * M = 1) :
    Function.Injective (fun x : ι → ZMod 2 => M *ᵥ x) := by
  intro x y hxy
  have H : N *ᵥ (M *ᵥ x) = N *ᵥ (M *ᵥ y) := congrArg (N *ᵥ ·) hxy
  simpa only [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] using H

end D5.S3.Factorization.QuadraticIdeals.FiniteLegendreSquareclassCertificate
