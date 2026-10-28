/- GID: D5/S3/ConceptDynamics/Coding/CountedGyrationPolynomial
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGyrationPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original counted orbits, order types, and integral polynomial lifts. -/

import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Classical

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

/-- Every R occurrence and every S occurrence is counted once. -/
theorem occurrence_card_sum {n m d : ℕ} [NeZero d] (w : VertexWord n m d) :
    (∑ e : Entry n m, Fintype.card (Occurrence w e)) = 2*d := by
  classical
  have hr : (∑ ij : Fin n × Fin m, Fintype.card (Occurrence w (Sum.inl ij))) = d := by
    calc
      _ = Fintype.card (Σ ij : Fin n × Fin m, Occurrence w (Sum.inl ij)) :=
        by simp only [Fintype.card_sigma]
      _ = Fintype.card (Fin d) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv (fun t : Fin d => (w.1 t,w.2 t)))
      _ = d := Fintype.card_fin d
  have hs : (∑ ji : Fin m × Fin n, Fintype.card (Occurrence w (Sum.inr ji))) = d := by
    calc
      _ = Fintype.card (Σ ji : Fin m × Fin n, Occurrence w (Sum.inr ji)) :=
        by simp only [Fintype.card_sigma]
      _ = Fintype.card (Fin d) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv (fun t : Fin d => (w.2 t,w.1 (t+1))))
      _ = d := Fintype.card_fin d
  rw [Fintype.sum_sum_type,hr,hs]
  omega

theorem widths_sum_le {n m d : ℕ} [NeZero d] {w : VertexWord n m d} (T : WordType w) :
    (∑ e : Entry n m, widths T e) ≤ 2*d := by
  classical
  calc
    _ ≤ ∑ e : Entry n m, Fintype.card (Occurrence w e) := by
      apply Finset.sum_le_sum
      intro e _
      exact Nat.le_of_lt_succ (T e).1.isLt
    _ = 2*d := occurrence_card_sum w

def typeFactorial {n m d : ℕ} [NeZero d] {w : VertexWord n m d} (T : WordType w) : ℕ :=
  ∏ e : Entry n m, (widths T e).factorial

theorem typeFactorial_pos {n m d : ℕ} [NeZero d] {w : VertexWord n m d} (T : WordType w) :
    0 < typeFactorial T := by
  classical
  exact Finset.prod_pos (fun e _ => Nat.factorial_pos _)

/-- Existing multinomial factorial divisibility is used at the actual
occurrence widths; their total is at most the 2d half-edge slots. -/
theorem typeFactorial_dvd {n m d : ℕ} [NeZero d] {w : VertexWord n m d} (T : WordType w) :
    typeFactorial T ∣ (2*d).factorial :=
  (Nat.prod_factorial_dvd_factorial_sum Finset.univ (widths T)).trans
    (Nat.factorial_dvd_factorial (widths_sum_le T))

/-- Unexpanded falling-factorial product, with integral coefficients. -/
def fallingEntry {n m : ℕ} (e : Entry n m) (k : ℕ) : MvPolynomial (Entry n m) ℤ :=
  ∏ a ∈ Finset.range k, (MvPolynomial.X e - MvPolynomial.C (a : ℤ))

/-- The rational binomial polynomial in one actual matrix-entry variable. -/
def binomialEntry {n m : ℕ} (e : Entry n m) (k : ℕ) : MvPolynomial (Entry n m) ℚ :=
  MvPolynomial.C ((k.factorial : ℚ)⁻¹) *
    MvPolynomial.map (Int.castRingHom ℚ) (fallingEntry e k)

theorem binomialEntry_eval_signed {n m : ℕ} (z : Entry n m → ℤ) (e : Entry n m) (k : ℕ) :
    MvPolynomial.eval (fun e => (z e : ℚ)) (binomialEntry e k) =
      ((Ring.choose (z e) k : ℤ) : ℚ) := by
  classical
  have hs : (descPochhammer ℤ k).smeval (z e : ℚ) =
      ∏ a ∈ Finset.range k, ((z e : ℚ) - (a : ℚ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval ℤ,
      Polynomial.eval₂_eq_eval_map,descPochhammer_map,descPochhammer_eval_eq_prod_range]
  have hf : MvPolynomial.eval (fun e => (z e : ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ) (fallingEntry e k)) =
        ∏ a ∈ Finset.range k, ((z e : ℚ) - (a : ℚ)) := by
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun e => (z e : ℚ))
      (fallingEntry e k) = _
    simp only [fallingEntry,map_prod,map_sub,MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C,map_intCast,map_natCast,Int.cast_natCast]
  calc
    _ = (k.factorial : ℚ)⁻¹ *
        ∏ a ∈ Finset.range k, ((z e : ℚ) - (a : ℚ)) := by
      rw [binomialEntry,map_mul,MvPolynomial.eval_C,hf]
    _ = Ring.choose (z e : ℚ) k := by
      rw [Ring.choose_eq_smul,smul_eq_mul,hs]
    _ = ((Ring.choose (z e) k : ℤ) : ℚ) :=
      (Ring.map_choose (Int.castRingHom ℚ) (z e) k).symm

/-- The same finite rank index and the same INTEGER forward weights as the
actual primitive-path quotient theorem. Matrix magnitudes are only variables. -/
def rationalGyrationPolynomial (n m d : ℕ) [NeZero d] : MvPolynomial (Entry n m) ℚ :=
  ∑ w : VertexWord n m d, ∑ T : WordType w,
    MvPolynomial.C ((wordWeight (sourceEdge w (widths T) (rankLabels T))
      (targetEdge w (widths T) (rankLabels T)) : ℤ) : ℚ) *
      ∏ e : Entry n m, binomialEntry e (widths T e)

def signedGyrationLift {n m d : ℕ} [NeZero d] (z : Entry n m → ℤ) : ℤ :=
  ∑ w : VertexWord n m d, ∑ T : WordType w,
    wordWeight (sourceEdge w (widths T) (rankLabels T))
      (targetEdge w (widths T) (rankLabels T)) *
        ∏ e : Entry n m, Ring.choose (z e) (widths T e)

/-- Integer values at EVERY signed integer tuple, obtained by Ring.choose;
there is no assumed integer-valuedness or finite-difference reconstruction. -/
theorem rationalGyrationPolynomial_eval_signed {n m d : ℕ} [NeZero d]
    (z : Entry n m → ℤ) :
    MvPolynomial.eval (fun e => (z e : ℚ)) (rationalGyrationPolynomial n m d) =
      (signedGyrationLift (d := d) z : ℚ) := by
  classical
  simp only [rationalGyrationPolynomial,signedGyrationLift,map_sum,map_mul,
    MvPolynomial.eval_C,map_prod,binomialEntry_eval_signed,
    Int.cast_sum,Int.cast_mul,Int.cast_prod]

/-- An explicit finite integral numerator: each summand uses the exact
integer quotient (2d)! / product_e(width_e!). No coefficients are expanded. -/
def integralGyrationNumerator (n m d : ℕ) [NeZero d] : MvPolynomial (Entry n m) ℤ :=
  ∑ w : VertexWord n m d, ∑ T : WordType w,
    MvPolynomial.C (wordWeight (sourceEdge w (widths T) (rankLabels T))
      (targetEdge w (widths T) (rankLabels T)) *
        (((2*d).factorial / typeFactorial T : ℕ) : ℤ)) *
          ∏ e : Entry n m, fallingEntry e (widths T e)

private theorem product_binomialEntry {n m d : ℕ} [NeZero d]
    {w : VertexWord n m d} (T : WordType w) :
    (∏ e : Entry n m, binomialEntry e (widths T e)) =
      MvPolynomial.C ((typeFactorial T : ℚ)⁻¹) *
        ∏ e : Entry n m,
          MvPolynomial.map (Int.castRingHom ℚ) (fallingEntry e (widths T e)) := by
  classical
  unfold binomialEntry
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod]
  congr 1
  rw [Finset.prod_inv_distrib,← Nat.cast_prod]
  rfl

private theorem factorialQuotient_rat {n m d : ℕ} [NeZero d]
    {w : VertexWord n m d} (T : WordType w) :
    (((2*d).factorial / typeFactorial T : ℕ) : ℚ) =
      ((2*d).factorial : ℚ) * (typeFactorial T : ℚ)⁻¹ := by
  have hmul := Nat.div_mul_cancel (typeFactorial_dvd T)
  have hrat : (((2*d).factorial / typeFactorial T : ℕ) : ℚ) *
      (typeFactorial T : ℚ) = ((2*d).factorial : ℚ) := by exact_mod_cast hmul
  have hn : (typeFactorial T : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (typeFactorial_pos T))
  simpa only [div_eq_mul_inv] using (eq_div_iff hn).mpr hrat

/-- Exact polynomial identity clearing the common denominator (2d)!. -/
theorem integralGyrationNumerator_map (n m d : ℕ) [NeZero d] :
    MvPolynomial.map (Int.castRingHom ℚ) (integralGyrationNumerator n m d) =
      MvPolynomial.C (((2*d).factorial : ℕ) : ℚ) * rationalGyrationPolynomial n m d := by
  classical
  simp only [integralGyrationNumerator,rationalGyrationPolynomial,map_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro T _
  rw [map_mul,MvPolynomial.map_C,map_prod,product_binomialEntry]
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast,
    factorialQuotient_rat, map_mul]
  ring

/-- Numerator evaluation at signed entries, with the integral lift on the
right. This follows from the explicit polynomial identity, not an evaluation
grid or an unproved coefficient-integrality assertion. -/
theorem integralGyrationNumerator_eval_signed {n m d : ℕ} [NeZero d]
    (z : Entry n m → ℤ) :
    MvPolynomial.eval z (integralGyrationNumerator n m d) =
      ((2*d).factorial : ℤ) * signedGyrationLift (d := d) z := by
  have h := congrArg (MvPolynomial.eval (fun e => (z e : ℚ)))
    (integralGyrationNumerator_map n m d)
  rw [MvPolynomial.eval_map] at h
  have he : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun e => (z e : ℚ))
      (integralGyrationNumerator n m d) =
        ((MvPolynomial.eval z (integralGyrationNumerator n m d) : ℤ) : ℚ) := by
    exact (MvPolynomial.eval₂_comp (Int.castRingHom ℚ) z _).symm
  rw [he,map_mul,MvPolynomial.eval_C,rationalGyrationPolynomial_eval_signed] at h
  exact_mod_cast h


end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
