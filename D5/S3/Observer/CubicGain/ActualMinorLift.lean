/- GID: D5/S3/Observer/CubicGain/ActualMinorLift
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/ActualMinorLift
   mirror-E: none(waiver:actual-minor-lift-continuation)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.GaussLemma]
   utility: none
   digest: Actual integer determinant polynomials and primitive gcd ratio bridge for the selected source minor. -/

import D5.S3.Observer.CubicGain.SelectedRootCommonZero
import D5.S3.Observer.CubicGain.SelectedMinorNonzero
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
noncomputable section

namespace D5.S3.Observer.CubicGain.ActualMinorLift

open Polynomial
open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.ExactW3Center
open D5.S3.Observer.CubicGain.SelectedRootCommonZero

/-! The source expressions are instantiated over `Polynomial ℤ`, so the outer
polynomial variable is `r` and every coefficient is an actual polynomial in
the source parameter `b`. -/

def sourceE0Coeff : Polynomial (Polynomial ℤ) :=
  sourceE0 (R := Polynomial ℤ) (Polynomial.X : Polynomial ℤ)

def sourceE1Coeff : Polynomial (Polynomial ℤ) :=
  sourceE1 (R := Polynomial ℤ) (Polynomial.X : Polynomial ℤ)

def literalRowCoeff (i : Fin 28) : Polynomial (Polynomial ℤ) :=
  if i.val < 14 then Polynomial.X ^ (13 - i.val) * sourceE0Coeff
  else Polynomial.X ^ (27 - i.val) * sourceE1Coeff

def literalMatrixCoeff : Matrix (Fin 28) (Fin 29) (Polynomial ℤ) :=
  fun i j => (literalRowCoeff i).coeff (28 - j.val)

def fixedMinorRCoeff : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  fun i j =>
    if h : j.val < 27 then literalMatrixCoeff i ⟨j.val, by omega⟩
    else literalMatrixCoeff i ⟨27, by omega⟩

def fixedMinorCCoeff : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  fun i j =>
    if h : j.val < 27 then literalMatrixCoeff i ⟨j.val, by omega⟩
    else literalMatrixCoeff i ⟨28, by omega⟩

def actualMinorA0 : Polynomial ℤ := (fixedMinorRCoeff).det
def actualMinorC0 : Polynomial ℤ := (fixedMinorCCoeff).det

def evalB (b : ℝ) : Polynomial ℤ →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) b

/-! This is the exact coefficient-level source bridge. -/
private theorem literalMatrixCoeff_eval (b : ℝ) :
    literalMatrixCoeff.map (evalB b) = literalMatrix b := by
  have h0 : sourceE0Coeff.map (evalB b) = sourceE0 b := by
    simp [sourceE0Coeff, sourceE0, evalB]
  have h1 : sourceE1Coeff.map (evalB b) = sourceE1 b := by
    simp [sourceE1Coeff, sourceE1, evalB]
  ext i j
  by_cases hi : i.val < 14
  · have hrow : (literalRowCoeff i).map (evalB b) = literalRow b i := by
      simp [literalRowCoeff, literalRow, hi, h0]
    change evalB b ((literalRowCoeff i).coeff (28 - j.val)) =
      (literalRow b i).coeff (28 - j.val)
    rw [← coeff_map, hrow]
  · have hrow : (literalRowCoeff i).map (evalB b) = literalRow b i := by
      simp [literalRowCoeff, literalRow, hi, h1]
    change evalB b ((literalRowCoeff i).coeff (28 - j.val)) =
      (literalRow b i).coeff (28 - j.val)
    rw [← coeff_map, hrow]

private theorem fixedMinorRCoeff_eval (b : ℝ) :
    fixedMinorRCoeff.map (evalB b) = fixedMinorR (literalMatrix b) := by
  ext i j
  change evalB b (fixedMinorRCoeff i j) = fixedMinorR (literalMatrix b) i j
  by_cases hj : j.val < 27
  · simp only [fixedMinorRCoeff, fixedMinorR, hj]
    exact congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i ⟨j.val, by omega⟩)
      (literalMatrixCoeff_eval b)
  · simp only [fixedMinorRCoeff, fixedMinorR, hj]
    exact congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i 27)
      (literalMatrixCoeff_eval b)

private theorem fixedMinorCCoeff_eval (b : ℝ) :
    fixedMinorCCoeff.map (evalB b) = fixedMinorC (literalMatrix b) := by
  ext i j
  change evalB b (fixedMinorCCoeff i j) = fixedMinorC (literalMatrix b) i j
  by_cases hj : j.val < 27
  · simp only [fixedMinorCCoeff, fixedMinorC, hj]
    exact congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i ⟨j.val, by omega⟩)
      (literalMatrixCoeff_eval b)
  · simp only [fixedMinorCCoeff, fixedMinorC, hj]
    exact congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i 28)
      (literalMatrixCoeff_eval b)

theorem actualMinorA0_eval (b : ℝ) :
    (actualMinorA0.map (Int.castRingHom ℝ)).eval b =
      Matrix.det (fixedMinorR (literalMatrix b)) := by
  simpa only [actualMinorA0, evalB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map] using
    (RingHom.map_det (evalB b) fixedMinorRCoeff).trans
      (congrArg Matrix.det (fixedMinorRCoeff_eval b))

theorem actualMinorC0_eval (b : ℝ) :
    (actualMinorC0.map (Int.castRingHom ℝ)).eval b =
      Matrix.det (fixedMinorC (literalMatrix b)) := by
  simpa only [actualMinorC0, evalB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map] using
    (RingHom.map_det (evalB b) fixedMinorCCoeff).trans
      (congrArg Matrix.det (fixedMinorCCoeff_eval b))

/-! Clearing denominators, taking the primitive part, and normalizing its
leading sign implements the source operation `pp_+` on nonzero rational
polynomials. The gcd itself is never evaluated by these proofs. -/


def positivePrimitive (f : ℚ[X]) : ℤ[X] :=
  normalize (IsLocalization.integerNormalization (nonZeroDivisors ℤ) f).primPart

private theorem positivePrimitive_primitive (f : ℚ[X]) : (positivePrimitive f).IsPrimitive := by
  exact Polynomial.isPrimitive_of_dvd (Polynomial.isPrimitive_primPart _)
    (normalize_associated _).dvd

private theorem positivePrimitive_pos (f : ℚ[X]) : 0 < (positivePrimitive f).leadingCoeff := by
  unfold positivePrimitive
  rw [Polynomial.leadingCoeff_normalize, ← Int.abs_eq_normalize]
  exact abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.primPart_ne_zero _))

private theorem positivePrimitive_associated {f : ℚ[X]} (hf : f ≠ 0) :
    Associated ((positivePrimitive f).map (Int.castRingHom ℚ)) f := by
  let n := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f
  have hn : n ≠ 0 := mt IsFractionRing.integerNormalization_eq_zero_iff.mp hf
  have hc : (n.content : ℚ) ≠ 0 := by
    exact_mod_cast (mt Polynomial.content_eq_zero_iff.mp hn)
  have hp : Associated (n.primPart.map (Int.castRingHom ℚ))
      (n.map (Int.castRingHom ℚ)) := by
    conv_rhs => rw [n.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    exact (associated_isUnit_mul_right_iff (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).2
      (Associated.refl _)
  obtain ⟨c, hc0, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f
  have hc' : (c : ℚ) ≠ 0 := by
    exact_mod_cast (nonZeroDivisors.ne_zero hc0)
  have hnmap : n.map (Int.castRingHom ℚ) = C (c : ℚ) * f := by
    have hcast : algebraMap ℤ ℚ = Int.castRingHom ℚ := Subsingleton.elim _ _
    change n.map (algebraMap ℤ ℚ) = c • f at he
    rw [hcast] at he
    simpa only [Polynomial.C_mul', Int.cast_smul_eq_zsmul] using he
  have hnf : Associated (n.map (Int.castRingHom ℚ)) f := by
    rw [hnmap]
    exact (associated_isUnit_mul_left_iff (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc'))).2
      (Associated.refl _)
  exact ((normalize_associated n.primPart).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).trans
    (hp.trans hnf)

private theorem positivePrimitive_gcd_factors (p q : ℤ[X])
    (hp : p ≠ 0) :
    ∃ A C : ℤ[X],
      p = positivePrimitive (gcd (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ))) * A ∧
      q = positivePrimitive (gcd (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ))) * C := by
  let g := gcd (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ))
  let h := positivePrimitive g
  have hg : g ≠ 0 := gcd_ne_zero_of_left ((Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℚ))).mpr hp)
  have hh : h.IsPrimitive := positivePrimitive_primitive g
  have ha : Associated (h.map (Int.castRingHom ℚ)) g := positivePrimitive_associated hg
  have hd₁ : h ∣ p := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast h p hh).2
    (ha.dvd.trans (gcd_dvd_left _ _))
  have hd₂ : h ∣ q := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast h q hh).2
    (ha.dvd.trans (gcd_dvd_right _ _))
  obtain ⟨A, hA⟩ := hd₁
  obtain ⟨C, hC⟩ := hd₂
  exact ⟨A, C, hA, hC⟩

private theorem associated_scalar {f g : ℚ[X]} (h : Associated f g) :
    ∃ u : ℚ, u ≠ 0 ∧ f = C u * g := by
  obtain ⟨u, hu⟩ := h.symm
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp u.isUnit
  exact ⟨c, hc.ne_zero, by rw [← hu, ← he, mul_comm]⟩

private theorem quotient_map {p h A : ℤ[X]} (hf : p = h * A) (hh : h ≠ 0) :
    p.map (Int.castRingHom ℚ) / h.map (Int.castRingHom ℚ) =
      A.map (Int.castRingHom ℚ) := by
  rw [hf, Polynomial.map_mul,
    mul_div_cancel_left₀ _ ((Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℚ))).mpr hh)]

private theorem eval_cast_tower (p : ℤ[X]) (b : ℝ) :
    ((p.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)).eval b = evalB b p := by
  have hc : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  rw [Polynomial.map_map, hc]
  exact (Polynomial.eval₂_eq_eval_map (Int.castRingHom ℝ)).symm

private theorem factor_ratio {p q h A C : ℤ[X]} (hp : p = h * A) (hq : q = h * C)
    (b r : ℝ) (hn : evalB b p ≠ 0) (hr : r * evalB b p + evalB b q = 0) :
    evalB b h ≠ 0 ∧ evalB b A ≠ 0 ∧ r = -evalB b C / evalB b A := by
  have he : evalB b p = evalB b h * evalB b A := by rw [hp, map_mul]
  have hne := mul_ne_zero_iff.mp (he ▸ hn)
  have hz : evalB b h * (r * evalB b A + evalB b C) = 0 := by
    calc
      _ = r * evalB b p + evalB b q := by rw [hp, hq, map_mul, map_mul]; ring
      _ = 0 := hr
  have hlin := (mul_eq_zero.mp hz).resolve_left hne.1
  exact ⟨hne.1, hne.2, (eq_div_iff hne.2).2 (by linarith)⟩

/-- The rational gcd of the actual two fixed determinant polynomials. -/
def actualGcdQ : ℚ[X] :=
  gcd (actualMinorA0.map (Int.castRingHom ℚ)) (actualMinorC0.map (Int.castRingHom ℚ))

/-- The positive primitive integer associate of the actual rational gcd. -/
def actualPrimitiveGcd : ℤ[X] := positivePrimitive actualGcdQ

/-- The exact source quotient `a₀/h`, formed over the rational polynomial ring. -/
def actualReducedA : ℚ[X] :=
  actualMinorA0.map (Int.castRingHom ℚ) / actualPrimitiveGcd.map (Int.castRingHom ℚ)

/-- The exact source quotient `c₀/h`, formed over the rational polynomial ring. -/
def actualReducedC : ℚ[X] :=
  actualMinorC0.map (Int.castRingHom ℚ) / actualPrimitiveGcd.map (Int.castRingHom ℚ)

attribute [irreducible] actualMinorA0 actualMinorC0 actualGcdQ actualPrimitiveGcd
  actualReducedA actualReducedC

/-- The actual selected lift is the ratio of the original source-normalized
fixed minors. Both source quotients have integer coefficients; the primitive
gcd and the reduced leading minor are nonzero at the selected root. -/
theorem selected_source_normalized_lift :
    actualPrimitiveGcd.IsPrimitive ∧ 0 < actualPrimitiveGcd.leadingCoeff ∧
    (∃ u : ℚ, u ≠ 0 ∧ actualPrimitiveGcd.map (Int.castRingHom ℚ) = C u * actualGcdQ) ∧
    ∃ A C : ℤ[X],
      actualMinorA0 = actualPrimitiveGcd * A ∧
      actualMinorC0 = actualPrimitiveGcd * C ∧
      actualReducedA = A.map (Int.castRingHom ℚ) ∧
      actualReducedC = C.map (Int.castRingHom ℚ) ∧
      evalB criticalRoot actualPrimitiveGcd ≠ 0 ∧
      ((actualReducedA.map (Rat.castHom ℝ)).eval criticalRoot) ≠ 0 ∧
      liftedR criticalRoot = -((actualReducedC.map (Rat.castHom ℝ)).eval criticalRoot) /
        ((actualReducedA.map (Rat.castHom ℝ)).eval criticalRoot) := by
  have hp_eval : evalB criticalRoot actualMinorA0 ≠ 0 := by
    rw [evalB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, actualMinorA0_eval]
    exact SelectedMinorNonzero.selected_minor_nonzero
  have hp : actualMinorA0 ≠ 0 := by
    intro hz
    exact hp_eval (by rw [hz, map_zero])
  have hg : actualGcdQ ≠ 0 := by
    rw [actualGcdQ]
    exact gcd_ne_zero_of_left
      ((Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℚ))).mpr hp)
  have hh : actualPrimitiveGcd.IsPrimitive := by
    rw [actualPrimitiveGcd]
    exact positivePrimitive_primitive _
  have hpos : 0 < actualPrimitiveGcd.leadingCoeff := by
    rw [actualPrimitiveGcd]
    exact positivePrimitive_pos _
  have hassoc : Associated (actualPrimitiveGcd.map (Int.castRingHom ℚ)) actualGcdQ := by
    rw [actualPrimitiveGcd]
    exact positivePrimitive_associated hg
  obtain ⟨A, C, hA, hC⟩ := positivePrimitive_gcd_factors actualMinorA0 actualMinorC0 hp
  have hnorm : positivePrimitive
      (gcd (actualMinorA0.map (Int.castRingHom ℚ)) (actualMinorC0.map (Int.castRingHom ℚ))) =
      actualPrimitiveGcd := by rw [actualPrimitiveGcd, actualGcdQ]
  rw [hnorm] at hA hC
  have hrel : liftedR criticalRoot * evalB criticalRoot actualMinorA0 +
      evalB criticalRoot actualMinorC0 = 0 := by
    simpa only [evalB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, actualMinorA0_eval, actualMinorC0_eval]
      using SelectedRootCommonZero.selected_root_common_zero.2.2.2.2.2
  obtain ⟨hh_eval, hA_eval, hratio⟩ := factor_ratio hA hC criticalRoot
    (liftedR criticalRoot) hp_eval hrel
  have hqa : actualReducedA = A.map (Int.castRingHom ℚ) := by
    rw [actualReducedA]
    exact quotient_map hA hh.ne_zero
  have hqc : actualReducedC = C.map (Int.castRingHom ℚ) := by
    rw [actualReducedC]
    exact quotient_map hC hh.ne_zero
  refine ⟨hh, hpos, associated_scalar hassoc, A, C, hA, hC, hqa, hqc, hh_eval, ?_, ?_⟩
  · rw [hqa, eval_cast_tower]
    exact hA_eval
  · rw [hqa, hqc, eval_cast_tower, eval_cast_tower]
    exact hratio

end D5.S3.Observer.CubicGain.ActualMinorLift
