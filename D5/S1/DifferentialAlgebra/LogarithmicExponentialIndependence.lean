/- GID: D5/S1/DifferentialAlgebra/LogarithmicExponentialIndependence
   generality: I
   mirror-B: D5/B/S1/DifferentialAlgebra/LogarithmicExponentialIndependence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.AlgebraicIndependent.Transcendental, mathlib/module/Mathlib.RingTheory.Algebraic.Integral, mathlib/module/Mathlib.Tactic.FinCases, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Algebraic independence of the formal variable, minus log of two minus its exponential, and the derivative. -/

import D5.S1.DifferentialAlgebra.ExponentialDifferentialField
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

attribute [local instance 2000] Algebra.toSMul

namespace D5.S1.DifferentialAlgebra.RationalPrimitiveIndependence

variable {K H : Type*} [Field K] [Field H] [Algebra K H] [CharZero H]

/-- The fractional linear transformation `e/(2-e)` preserves transcendence. -/
theorem mobius_transcendental {e : H} (he : Transcendental K e) :
    Transcendental K (e / (2 - e)) := by
  let g : H := e / (2 - e)
  have htwo : IsAlgebraic K (2 : H) := by
    simpa only [map_ofNat] using
      (isAlgebraic_algebraMap (R := K) (A := H) (2 : K))
  have hden : (2 : H) - e ≠ 0 := by
    intro h
    have heq : e = (2 : H) := (sub_eq_zero.mp h).symm
    apply he
    simpa only [heq] using htwo
  have hrel : g * (2 - e) = e := div_mul_cancel₀ e hden
  have hsum : (1 + g) * (2 - e) = 2 := by
    rw [add_mul, one_mul, hrel]
    ring
  have hone : 1 + g ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsum
    exact (two_ne_zero : (2 : H) ≠ 0) hsum.symm
  have hback : e = 2 * g / (1 + g) := by
    apply (eq_div_iff hone).mpr
    rw [mul_sub] at hrel
    have hrel' : g * 2 = e + g * e := sub_eq_iff_eq_add.mp hrel
    calc
      e * (1 + g) = e + g * e := by ring
      _ = g * 2 := hrel'.symm
      _ = 2 * g := mul_comm _ _
  intro hg
  change IsAlgebraic K g at hg
  apply he
  have hvalue : IsAlgebraic K (2 * g / (1 + g)) := by
    rw [div_eq_mul_inv]
    exact (htwo.mul hg).mul
      ((isAlgebraic_one (R := K) (A := H)).add hg).inv
  exact hback.symm ▸ hvalue

variable {Q0 K0 H0 L : Type*} [Field Q0] [Field K0] [Field H0] [Field L]
  [CharZero H0]
  [Algebra Q0 K0] [Algebra Q0 H0] [Algebra Q0 L]
  [Algebra K0 H0] [Algebra K0 L] [Algebra H0 L]
  [IsScalarTower Q0 K0 H0] [IsScalarTower Q0 K0 L]
  [IsScalarTower Q0 H0 L] [IsScalarTower K0 H0 L]

/-- Three successive transcendental coordinates remain algebraically independent when
the middle coordinate is replaced by `e/(2-e)`. -/
theorem rational_primitive_independent (x : K0) (e : H0) (f : L)
    (hx : Transcendental Q0 x) (he : Transcendental K0 e)
    (hf : Transcendental H0 f) :
    AlgebraicIndependent Q0
      ![algebraMap K0 L x, f, algebraMap H0 L (e / (2 - e))] := by
  have hx' : AlgebraicIndependent Q0 (fun _ : Fin 1 => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hg' : AlgebraicIndependent K0 (fun _ : Fin 1 => e / (2 - e)) :=
    algebraicIndependent_unique_type_iff.mpr (mobius_transcendental he)
  let pair : Fin 1 ⊕ Fin 1 → H0 :=
    Sum.elim (fun _ => e / (2 - e)) (algebraMap K0 H0 ∘ fun _ => x)
  have hpair : AlgebraicIndependent Q0 pair := hx'.sumElim_comp hg'
  have hf' : AlgebraicIndependent H0 (fun _ : Fin 1 => f) :=
    algebraicIndependent_unique_type_iff.mpr hf
  let triple : Fin 1 ⊕ (Fin 1 ⊕ Fin 1) → L :=
    Sum.elim (fun _ => f) (algebraMap H0 L ∘ pair)
  have htriple : AlgebraicIndependent Q0 triple := hpair.sumElim_comp hf'
  let coord : Fin 3 → Fin 1 ⊕ (Fin 1 ⊕ Fin 1) :=
    ![Sum.inr (Sum.inr 0), Sum.inl 0, Sum.inr (Sum.inl 0)]
  have hcoord : Function.Injective coord := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [coord]
  have hresult := htriple.comp coord hcoord
  have hfamily : triple ∘ coord =
      ![algebraMap K0 L x, f, algebraMap H0 L (e / (2 - e))] := by
    funext i
    fin_cases i <;>
      simp [triple, pair, coord, Function.comp_def,
        ← IsScalarTower.algebraMap_apply K0 H0 L]
  rwa [hfamily] at hresult

#print axioms rational_primitive_independent

end D5.S1.DifferentialAlgebra.RationalPrimitiveIndependence

namespace D5.S1.DifferentialAlgebra.LogarithmicExponentialIndependence

open ExponentialDifferentialField
open LogarithmicExponentialSeries

/-- The formal variable, the normalized series `-log(2-exp X)`, and its derivative
are algebraically independent over the rationals. -/
theorem algebraically_independent :
    AlgebraicIndependent ℚ
      ![(PowerSeries.X : PowerSeries ℚ), F, PowerSeries.derivative F] := by
  have hx : Transcendental ℚ (RatFunc.X : K) := by
    have ht := RatFunc.transcendental_X (K := ℚ)
    have ha : RatFunc.instAlgebraOfPolynomial ℚ ℚ =
        (inferInstance : Algebra ℚ K) := Subsingleton.elim _ _
    rw [ha] at ht
    exact ht
  have hi := RationalPrimitiveIndependence.rational_primitive_independent
    (Q0 := ℚ) (K0 := K) (H0 := H) (L := L)
    (RatFunc.X : K) (RatFunc.X : H) logImage
    hx RatFunc.transcendental_X
    logImage_transcendental
  apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom ℚ (PowerSeries ℚ) L)
  have hfamily :
      (IsScalarTower.toAlgHom ℚ (PowerSeries ℚ) L) ∘
          ![(PowerSeries.X : PowerSeries ℚ), F, PowerSeries.derivative F] =
        ![algebraMap K L RatFunc.X, logImage,
          algebraMap H L (RatFunc.X / (2 - RatFunc.X))] := by
    funext i
    fin_cases i
    · change algebraMap (PowerSeries ℚ) L PowerSeries.X = algebraMap K L RatFunc.X
      exact kX_image.symm
    · rfl
    · change algebraMap (PowerSeries ℚ) L (PowerSeries.derivative F) =
        algebraMap H L (RatFunc.X / (2 - RatFunc.X))
      exact rational_image.symm
  rw [hfamily]
  exact hi

#print axioms algebraically_independent

end D5.S1.DifferentialAlgebra.LogarithmicExponentialIndependence
