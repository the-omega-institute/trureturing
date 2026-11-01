/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted occupation estimates for the finite bilinear squeezed vacuum. -/

import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
The coefficients and factorial weights are the native polynomial Gaussian
coefficients and factorial Fock weights. Pairings in this module are bilinear;
there is no complex conjugation. The finite mode type may be empty.

The vacuum identity is the classical squeezed Gaussian/Bargmann-Wick
identity. Finite field sewing, Gram transport, countable limits and physical
realization are separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Ring

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum

open MvPolynomial
open FactorialFockQuadraticEstimate
open FactorialFockMetric (weight)

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

private theorem quadratic_smul (A : Matrix I I ℂ) (c : ℂ) :
    quadratic (c • A) = c • quadratic A := by
  unfold quadratic
  rw [smul_comm c]
  congr 1
  simp only [Finset.smul_sum, smul_smul, Matrix.smul_apply, smul_eq_mul]

private theorem gaussianCoefficient_smul (A : Matrix I I ℂ) (c : ℂ) (d : I →₀ ℕ) :
    gaussianCoefficient (c • A) d = c ^ (d.degree / 2) * gaussianCoefficient A d := by
  simp only [gaussianCoefficient, gaussianPiece, quadratic_smul, smul_pow,
    coeff_smul, smul_eq_mul]
  ring

private theorem polynomial_geometric_bound {s : ℝ} (hs : 1 < s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n + 1 : ℝ) ^ k ≤ C * s ^ n := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hr : ‖s⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
                            exact inv_lt_one_of_one_lt₀ hs
  have hsum := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr
  let T : ℝ := ∑' n : ℕ, (n : ℝ) ^ k * (s⁻¹) ^ n
  have hT : 0 ≤ T := tsum_nonneg (fun n => by positivity)
  refine ⟨s * T, mul_nonneg hs0.le hT, ?_⟩
  intro n
  have hn : (n + 1 : ℝ) ^ k * (s⁻¹) ^ (n + 1) ≤ T := by
    simpa only [T, Nat.cast_add, Nat.cast_one] using
      hsum.le_tsum (n + 1) (fun m _ => by positivity)
  have hh := mul_le_mul_of_nonneg_right hn (pow_nonneg hs0.le (n + 1))
  calc
    _ = ((n + 1 : ℝ) ^ k * (s⁻¹) ^ (n + 1)) * s ^ (n + 1) := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow, mul_one]
    _ ≤ T * s ^ (n + 1) := hh
    _ = _ := by rw [pow_succ]; ring

/-- Every fixed polynomial occupation weight is summable for the actual
Gaussian coefficients of a symmetric strict Euclidean contraction. -/
private theorem weighted_occupation_summable (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) (k : ℕ) :
    Summable (fun d : I →₀ ℕ => (d.degree + 1 : ℝ) ^ k *
      (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2) := by
  let a : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
  have ha : 0 ≤ a := norm_nonneg _
  let c : ℝ := 2 / (1 + a)
  have hden : 0 < 1 + a := by positivity
  have hc : 1 < c := (lt_div_iff₀ hden).2 (by dsimp [a]; linarith)
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hca : c * a < 1 := by
    dsimp [c]
    rw [div_mul_eq_mul_div, div_lt_one hden]
    dsimp [a]
    linarith
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((c : ℂ) • A)‖ = c * a := by
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hscaled := occupation_summable ((c : ℂ) • A)
    (fun i j => by simp only [Matrix.smul_apply]; rw [hsym i j])
    (mul_nonneg hc0.le ha) hca hnorm.le
  obtain ⟨C, hC, hbound⟩ := polynomial_geometric_bound (show 1 < c ^ 2 by nlinarith) k
  refine Summable.of_nonneg_of_le (fun d => by positivity)
    ?_ (hscaled.mul_left ((2 : ℝ) ^ k * C))
  intro d
  by_cases hodd : d.degree % 2 = 1
  · simp only [gaussianCoefficient_odd A d hodd, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero]
    positivity
  · have heven : d.degree = 2 * (d.degree / 2) := by omega
    have hp : (d.degree + 1 : ℝ) ^ k ≤ (2 : ℝ) ^ k *
        (C * (c ^ 2) ^ (d.degree / 2)) := by
      calc
        _ ≤ (2 * (((d.degree / 2 : ℕ) : ℝ) + 1)) ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          have hh : (d.degree : ℝ) = 2 * (d.degree / 2 : ℕ) := by exact_mod_cast heven
          linarith
        _ = (2 : ℝ) ^ k * (((d.degree / 2 : ℕ) : ℝ) + 1) ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound _) (by positivity)
    rw [gaussianCoefficient_smul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc0]
    have hh := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2 by positivity)
    have hpow : (c ^ 2) ^ (d.degree / 2) = (c ^ (d.degree / 2)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow] at hh
    convert hh using 1 <;> ring

private theorem weight_add_le (d α : I →₀ ℕ) :
    weight (d + α) ≤ weight d * ((α.degree + 1) * (d.degree + 1)) ^ α.degree := by
  classical
  have hw (e : I →₀ ℕ) : weight e = ∏ i, (e i).factorial :=
    FactorialFockMetric.weight_eq_prod e Finset.univ (Finset.subset_univ _)
  rw [hw, hw, α.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro i hi
  rw [Finsupp.add_apply, ← Nat.factorial_mul_ascFactorial]
  apply Nat.mul_le_mul_left
  apply (Nat.ascFactorial_le_pow_add _ _).trans
  apply Nat.pow_le_pow_left
  have hd := Finsupp.le_degree i d
  have hα : α i ≤ ∑ i, α i := by simpa [Finsupp.degree_eq_sum] using Finsupp.le_degree i α
  nlinarith

private theorem shifted_weighted_square_summable (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) (α : I →₀ ℕ) (k : ℕ) :
    Summable (fun d : I →₀ ℕ =>
      (d.degree + 1 : ℝ) ^ k * (weight (d + α) : ℝ) *
        ‖gaussianCoefficient A d‖ ^ 2) := by
  have hs := (weighted_occupation_summable A hsym hA (α.degree + k)).mul_left
    ((α.degree + 1 : ℝ) ^ α.degree)
  apply Summable.of_nonneg_of_le (fun d => by positivity) _ hs
  intro d
  have hb : (weight (d + α) : ℝ) ≤ (weight d : ℝ) *
      ((α.degree + 1 : ℝ) * (d.degree + 1 : ℝ)) ^ α.degree := by
    exact_mod_cast weight_add_le d α
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (d.degree + 1 : ℝ) ^ k * ‖gaussianCoefficient A d‖ ^ 2 by positivity)
  simp only [mul_pow, pow_add] at hh ⊢
  convert hh using 1 <;> ring

/-- The actual bilinear pairing with any fixed creation monomial is
absolutely summable. The occupation shift is injective, with no positivity
or entrywise majorant assumption on either complex symmetric matrix. -/
private theorem insertion_norm_summable (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) (α : I →₀ ℕ) :
    Summable (fun d : I →₀ ℕ => ‖(weight (d + α) : ℂ) *
      gaussianCoefficient A d * gaussianCoefficient B (d + α)‖) := by
  have hsA := shifted_weighted_square_summable A hAsym hA α 0
  simp only [pow_zero, one_mul] at hsA
  have hsB := (occupation_summable B hBsym (norm_nonneg _) hB le_rfl).comp_injective
    (show Function.Injective (fun d : I →₀ ℕ => d + α) from add_left_injective α)
  apply Summable.of_nonneg_of_le (fun d => norm_nonneg _) _ (hsA.add hsB)
  intro d
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hu := norm_nonneg (gaussianCoefficient A d)
  have hv := norm_nonneg (gaussianCoefficient B (d + α))
  have hh : ‖gaussianCoefficient A d‖ * ‖gaussianCoefficient B (d + α)‖ ≤
      ‖gaussianCoefficient A d‖ ^ 2 + ‖gaussianCoefficient B (d + α)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖gaussianCoefficient A d‖ - ‖gaussianCoefficient B (d + α)‖)]
  simpa only [mul_add, mul_assoc, Function.comp_apply] using
    mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (weight (d + α)))

private theorem degree_sub_single (d : I →₀ ℕ) (i : I) (hi : d i ≠ 0) :
    (d - Finsupp.single i 1).degree + 1 = d.degree := by
  have he := tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
  have hh := congrArg Finsupp.degree (show d - Finsupp.single i 1 +
    Finsupp.single i 1 = d from he)
  simpa using hh

private def loweredCoefficient (A : Matrix I I ℂ) (i : I) (d : I →₀ ℕ) : ℂ :=
  if d i = 0 then 0 else gaussianCoefficient A (d - Finsupp.single i 1)

private theorem gaussianCoefficient_step (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) (i : I) (d : I →₀ ℕ) :
    gaussianCoefficient A (d + Finsupp.single i 1) * (d i + 1 : ℂ) =
      ∑ j, A i j * loweredCoefficient A j d := by
  have hdeg : (d + Finsupp.single i 1).degree = d.degree + 1 := by simp
  by_cases hodd : d.degree % 2 = 1
  · have hd : d.degree = 2 * (d.degree / 2) + 1 := by omega
    rw [gaussianCoefficient_even A _ (d.degree / 2 + 1) (by omega)]
    rw [gaussianPiece_coefficient_step A hsym]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_X_mul']
    by_cases hz : d j = 0
    · simp [loweredCoefficient, hz, Finsupp.mem_support_iff]
    · have hsub := degree_sub_single d j hz
      simp only [Finsupp.mem_support_iff, hz, ne_eq, not_false_eq_true, ite_true,
        loweredCoefficient, ite_false]
      rw [gaussianCoefficient_even A _ (d.degree / 2) (by omega)]
  · rw [gaussianCoefficient_odd A _ (by omega), zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hz : d j = 0
    · simp [loweredCoefficient, hz]
    · have hsub := degree_sub_single d j hz
      simp only [loweredCoefficient, hz, ite_false]
      rw [gaussianCoefficient_odd A _ (by omega), mul_zero]

private def occupationShift (i : I) : (I →₀ ℕ) ≃ {d : I →₀ ℕ // 0 < d i} where
  toFun d := ⟨d + Finsupp.single i 1, by simp⟩
  invFun d := d.val - Finsupp.single i 1
  left_inv d := add_tsub_cancel_right d _
  right_inv d := by
    apply Subtype.ext
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr d.property)

private theorem tsum_shift (i : I) (f : (I →₀ ℕ) → ℂ)
    (hzero : ∀ d, d i = 0 → f d = 0) :
    (∑' d, f (d + Finsupp.single i 1)) = ∑' d, f d := by
  calc
    _ = ∑' d : {d : I →₀ ℕ // 0 < d i}, f d :=
      (occupationShift i).tsum_eq (fun d => f d.val)
    _ = _ := tsum_subtype_eq_of_support_subset (by
      intro d hd
      have hn : d i ≠ 0 := by intro hz; exact hd (hzero d hz)
      exact Nat.pos_of_ne_zero hn)

/-- The native all-occupation bilinear pairing with a creation monomial. -/
def insertion (A B : Matrix I I ℂ) (α : I →₀ ℕ) : ℂ :=
  ∑' d : I →₀ ℕ, (weight (d + α) : ℂ) *
    gaussianCoefficient A d * gaussianCoefficient B (d + α)

private def insertionDerivativeTerm (A B : Matrix I I ℂ) (α d : I →₀ ℕ) (t : ℂ) : ℂ :=
  (weight (d + α) : ℂ) *
    ((d.degree / 2 : ℕ) * t ^ (d.degree / 2 - 1) * gaussianCoefficient A d) *
    gaussianCoefficient B (d + α)

private theorem insertionTerm_hasDerivAt (A B : Matrix I I ℂ) (α d : I →₀ ℕ) (t : ℂ) :
    HasDerivAt (fun z : ℂ => (weight (d + α) : ℂ) *
      gaussianCoefficient (z • A) d * gaussianCoefficient B (d + α))
      (insertionDerivativeTerm A B α d t) t := by
  simpa only [gaussianCoefficient_smul, insertionDerivativeTerm, mul_assoc] using
    (((hasDerivAt_pow (d.degree / 2) t).mul_const (gaussianCoefficient A d)).const_mul
      (weight (d + α) : ℂ)).mul_const (gaussianCoefficient B (d + α))

private theorem coefficientDerivative_bound (A : Matrix I I ℂ) (d : I →₀ ℕ)
    {S : ℝ} (hS : 1 < S) {t : ℂ} (ht : ‖t‖ ≤ S) :
    ‖(d.degree / 2 : ℕ) * t ^ (d.degree / 2 - 1) * gaussianCoefficient A d‖ ≤
      (d.degree + 1 : ℝ) * ‖gaussianCoefficient ((S : ℂ) • A) d‖ := by
  have hS0 : 0 < S := zero_lt_one.trans hS
  simp only [gaussianCoefficient_smul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hS0, Complex.norm_natCast]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hn : ((d.degree / 2 : ℕ) : ℝ) ≤ d.degree + 1 := by
    exact_mod_cast (show d.degree / 2 ≤ d.degree + 1 by omega)
  have hp : ‖t‖ ^ (d.degree / 2 - 1) ≤ S ^ (d.degree / 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) ht _).trans
      (pow_le_pow_right₀ hS.le (Nat.sub_le _ _))
  exact mul_le_mul hn hp (by positivity) (by positivity)

/-- A uniform summable derivative majorant on a complex neighborhood of
[0,1]. The derivative at zero is the derivative of a polynomial, with no
division by the scaling parameter. -/
private theorem insertion_hasDerivAt (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    {S : ℝ} (hS : 1 < S)
    (hSA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((S : ℂ) • A)‖ < 1)
    (α : I →₀ ℕ) {t : ℂ} (ht : ‖t‖ < S) :
    HasDerivAt (fun z : ℂ => insertion (z • A) B α)
      (∑' d : I →₀ ℕ, insertionDerivativeTerm A B α d t) t := by
  let u : (I →₀ ℕ) → ℝ := fun d => (weight (d + α) : ℝ) *
    ((d.degree + 1 : ℝ) ^ 2 * ‖gaussianCoefficient ((S : ℂ) • A) d‖ ^ 2 +
      ‖gaussianCoefficient B (d + α)‖ ^ 2)
  have hscaledSym : ∀ i j, ((S : ℂ) • A) i j = ((S : ℂ) • A) j i := by
    intro i j
    simp only [Matrix.smul_apply]
    rw [hAsym i j]
  have hsA := shifted_weighted_square_summable ((S : ℂ) • A) hscaledSym hSA α 2
  have hsB := (occupation_summable B hBsym (norm_nonneg _) hB le_rfl).comp_injective
    (show Function.Injective (fun d : I →₀ ℕ => d + α) from add_left_injective α)
  have hu : Summable u := by
    convert hsA.add hsB using 1
    funext d
    dsimp [u]
    ring
  have hcoefficient (z : ℂ) (hz : ‖z‖ ≤ S) (d : I →₀ ℕ) :
      ‖(weight (d + α) : ℂ) * gaussianCoefficient (z • A) d *
        gaussianCoefficient B (d + α)‖ ≤
      ‖(weight (d + α) : ℂ) * gaussianCoefficient ((S : ℂ) • A) d *
        gaussianCoefficient B (d + α)‖ := by
    have hc : ‖gaussianCoefficient (z • A) d‖ ≤
        ‖gaussianCoefficient ((S : ℂ) • A) d‖ := by
      simp only [gaussianCoefficient_smul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hS)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (norm_nonneg _)) (norm_nonneg _)
  have hbase := (Summable.of_nonneg_of_le (fun d => norm_nonneg _)
    (hcoefficient 1 (by simpa using hS.le))
    (insertion_norm_summable ((S : ℂ) • A) B hscaledSym hBsym hSA hB α)).of_norm
  have hb (d : I →₀ ℕ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) S) :
      ‖insertionDerivativeTerm A B α d z‖ ≤ u d := by
    have hdz := coefficientDerivative_bound A d hS
      (show ‖z‖ ≤ S from (by simpa using hz : ‖z‖ < S).le)
    have hsq := sq_nonneg ((d.degree + 1 : ℝ) *
      ‖gaussianCoefficient ((S : ℂ) • A) d‖ - ‖gaussianCoefficient B (d + α)‖)
    rw [insertionDerivativeTerm, norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (weight (d + α) : ℝ) *
          ((d.degree + 1 : ℝ) * ‖gaussianCoefficient ((S : ℂ) • A) d‖) *
            ‖gaussianCoefficient B (d + α)‖ := by gcongr
      _ ≤ u d := by
        dsimp [u]
        have hh := mul_le_mul_of_nonneg_left (show
          ((d.degree + 1 : ℝ) * ‖gaussianCoefficient ((S : ℂ) • A) d‖) *
              ‖gaussianCoefficient B (d + α)‖ ≤
            (d.degree + 1 : ℝ) ^ 2 * ‖gaussianCoefficient ((S : ℂ) • A) d‖ ^ 2 +
              ‖gaussianCoefficient B (d + α)‖ ^ 2 by nlinarith)
          (Nat.cast_nonneg (weight (d + α)))
        convert hh using 1 <;> simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), mul_assoc] <;> rfl
  apply hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) S).isPreconnected
    (fun d z _ => insertionTerm_hasDerivAt A B α d z) hb
    (y₀ := (1 : ℂ)) (by simpa using hS)
    hbase
    (by simpa using ht)

def created (α : I →₀ ℕ) (f : (I →₀ ℕ) → ℂ) (d : I →₀ ℕ) : ℂ :=
  if α ≤ d then f (d - α) else 0

theorem created_add (α β : I →₀ ℕ) (f : (I →₀ ℕ) → ℂ) :
    created α (created β f) = created (α + β) f := by
  funext d
  by_cases ha : α ≤ d
  · have hb : β ≤ d - α ↔ α + β ≤ d := by
      simpa only [add_comm β α] using (le_tsub_iff_right ha : β ≤ d - α ↔ β + α ≤ d)
    by_cases hab : α + β ≤ d
    · simp [created, ha, hab, hb.mpr hab, tsub_add_eq_tsub_tsub]
    · have hnot : ¬β ≤ d - α := fun h => hab (hb.mp h)
      simp [created, ha, hab, hnot]
  · have hab : ¬α + β ≤ d := fun h => ha (le_trans le_self_add h)
    simp [created, ha, hab]

theorem created_zero (f : (I →₀ ℕ) → ℂ) : created 0 f = f := by
  funext d
  simp [created]

theorem created_single (i : I) (f : (I →₀ ℕ) → ℂ) (d : I →₀ ℕ) :
    created (Finsupp.single i 1) f d = if d i = 0 then 0 else f (d - Finsupp.single i 1) := by
  by_cases hi : d i = 0 <;> simp [created, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, hi]

theorem created_square_summable (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) (α : I →₀ ℕ) :
    Summable (fun d : I →₀ ℕ => (weight d : ℝ) *
      ‖created α (gaussianCoefficient A) d‖ ^ 2) := by
  apply ((add_left_injective α).summable_iff ?_).1
  · change Summable (fun d : I →₀ ℕ => (weight (d + α) : ℝ) *
      ‖created α (gaussianCoefficient A) (d + α)‖ ^ 2)
    simpa only [created, le_add_self, ite_true,
      add_tsub_cancel_right, pow_zero, one_mul] using
      shifted_weighted_square_summable A hsym hA α 0
  · intro d hd
    have hnot : ¬α ≤ d := by
      intro hle
      exact hd ⟨d - α, tsub_add_cancel_of_le hle⟩
    simp [created, hnot]

theorem created_pair_summable (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) (α β : I →₀ ℕ) :
    Summable (fun d : I →₀ ℕ => (weight d : ℂ) *
      created α (gaussianCoefficient A) d * created β (gaussianCoefficient B) d) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun d => norm_nonneg _)
    _ ((created_square_summable A hAsym hA α).add
      (created_square_summable B hBsym hB β))
  intro d
  simp only [norm_mul, Complex.norm_natCast]
  have hs := sq_nonneg (‖created α (gaussianCoefficient A) d‖ -
    ‖created β (gaussianCoefficient B) d‖)
  have hw : 0 ≤ (weight d : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hw hs]

def pairing (f g : (I →₀ ℕ) → ℂ) : ℂ :=
  ∑' d : I →₀ ℕ, (weight d : ℂ) * f d * g d

def annihilate (i : I) (f : (I →₀ ℕ) → ℂ) (d : I →₀ ℕ) : ℂ :=
  (d i + 1 : ℂ) * f (d + Finsupp.single i 1)

theorem pairing_comm (f g : (I →₀ ℕ) → ℂ) : pairing f g = pairing g f := by
  apply tsum_congr
  intro d
  ring

theorem pairing_creation_annihilation (i : I) (f g : (I →₀ ℕ) → ℂ) :
    pairing (created (Finsupp.single i 1) f) g = pairing f (annihilate i g) := by
  unfold pairing
  rw [← tsum_shift i (fun d => (weight d : ℂ) *
    created (Finsupp.single i 1) f d * g d) (by
      intro d hd
      simp [created_single, hd])]
  apply tsum_congr
  intro d
  simp only [created_single, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    add_tsub_cancel_right, FactorialFockMetric.weight_add_single,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, annihilate]
  ring

theorem gaussian_annihilate (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) (i : I) :
    annihilate i (gaussianCoefficient A) = fun d =>
      ∑ j, A i j * created (Finsupp.single j 1) (gaussianCoefficient A) d := by
  funext d
  simpa only [annihilate, created_single, loweredCoefficient, mul_comm] using
    gaussianCoefficient_step A hsym i d

private theorem annihilate_creation (i j : I) (f : (I →₀ ℕ) → ℂ) :
    annihilate i (created (Finsupp.single j 1) f) = fun d =>
      (if i = j then f d else 0) + created (Finsupp.single j 1) (annihilate i f) d := by
  funext d
  by_cases hij : i = j
  · subst j
    by_cases hi : d i = 0
    · simp [annihilate, created_single, hi]
    · have hcancel := Finsupp.sub_add_single_one_cancel hi
      have hn : (d i - 1) + 1 = d i := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)
      simp only [annihilate, created_single, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
        add_tsub_cancel_right, ite_true, hi, Finsupp.tsub_apply, hn, hcancel]
      push_cast
      have hnC : ((d i - 1 : ℕ) : ℂ) + 1 = (d i : ℂ) := by exact_mod_cast hn
      linear_combination -f d * hnC
  · by_cases hj : d j = 0
    · simp [annihilate, created_single, hij, Ne.symm hij, hj]
    · simp only [annihilate, created_single, Finsupp.add_apply, Finsupp.single_apply,
        hij, Ne.symm hij, ite_false, add_zero, hj, Finsupp.tsub_apply, tsub_zero,
        zero_add, Finsupp.sub_single_one_add hj]

private theorem pairing_created (A B : Matrix I I ℂ) (α : I →₀ ℕ) :
    pairing (created α (gaussianCoefficient A)) (gaussianCoefficient B) = insertion A B α := by
  unfold pairing insertion
  symm
  have he := (add_left_injective α).tsum_eq (f := fun d : I →₀ ℕ =>
    (weight d : ℂ) * created α (gaussianCoefficient A) d * gaussianCoefficient B d) (by
      intro d hd
      by_contra hn
      have hnot : ¬α ≤ d := fun hle => hn ⟨d - α, tsub_add_cancel_of_le hle⟩
      exact hd (by simp [created, hnot]))
  simpa only [created, le_add_self, ite_true, add_tsub_cancel_right] using he

theorem pairing_const_right (c : ℂ) (f g : (I →₀ ℕ) → ℂ) :
    pairing f (fun d => c * g d) = c * pairing f g := by
  unfold pairing
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  ring

theorem pairing_sum_right (f : (I →₀ ℕ) → ℂ) (g : I → (I →₀ ℕ) → ℂ)
    (hs : ∀ i, Summable (fun d : I →₀ ℕ => (weight d : ℂ) * f d * g i d)) :
    pairing f (fun d => ∑ i, g i d) = ∑ i, pairing f (g i) := by
  unfold pairing
  simp only [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => hs i)

private theorem pairing_gaussian_annihilate (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) (α : I →₀ ℕ) (i : I) :
    pairing (created α (gaussianCoefficient A)) (annihilate i (gaussianCoefficient B)) =
      ∑ j, B i j * pairing (created α (gaussianCoefficient A))
        (created (Finsupp.single j 1) (gaussianCoefficient B)) := by
  rw [gaussian_annihilate B hBsym, pairing_sum_right]
  · simp only [pairing_const_right]
  · intro j
    convert (created_pair_summable A B hAsym hBsym hA hB α (Finsupp.single j 1)).mul_left
      (B i j) using 1
    funext d
    ring

theorem created_sum (α : I →₀ ℕ) (f : I → (I →₀ ℕ) → ℂ) :
    created α (fun d => ∑ j, f j d) = fun d => ∑ j, created α (f j) d := by
  funext d
  by_cases h : α ≤ d <;> simp [created, h]

theorem created_const (α : I →₀ ℕ) (c : ℂ) (f : (I →₀ ℕ) → ℂ) :
    created α (fun d => c * f d) = fun d => c * created α f d := by
  funext d
  by_cases h : α ≤ d <;> simp [created, h]

private theorem pairing_annihilate_created (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) (i j : I) :
    pairing (annihilate i (created (Finsupp.single j 1) (gaussianCoefficient A)))
        (gaussianCoefficient B) =
      (if i = j then insertion A B 0 else 0) +
        ∑ l, A i l * insertion A B (Finsupp.single j 1 + Finsupp.single l 1) := by
  rw [annihilate_creation, gaussian_annihilate A hAsym]
  simp_rw [created_sum, created_const, created_add]
  let f : (I →₀ ℕ) → ℂ := fun d => if i = j then gaussianCoefficient A d else 0
  let g : (I →₀ ℕ) → ℂ := fun d => ∑ l, A i l *
    created (Finsupp.single j 1 + Finsupp.single l 1) (gaussianCoefficient A) d
  have hf : Summable (fun d : I →₀ ℕ => (weight d : ℂ) * f d * gaussianCoefficient B d) := by
    dsimp [f]
    split_ifs
    · simpa only [created_zero] using created_pair_summable A B hAsym hBsym hA hB 0 0
    · simp
  have hterms (l : I) : Summable (fun d : I →₀ ℕ => (weight d : ℂ) *
      (A i l * created (Finsupp.single j 1 + Finsupp.single l 1) (gaussianCoefficient A) d) *
        gaussianCoefficient B d) := by
    convert (created_pair_summable A B hAsym hBsym hA hB
      (Finsupp.single j 1 + Finsupp.single l 1) 0).mul_left (A i l) using 1
    funext d
    rw [created_zero]
    ring
  have hg : Summable (fun d : I →₀ ℕ => (weight d : ℂ) * g d * gaussianCoefficient B d) := by
    simpa only [g, Finset.mul_sum, Finset.sum_mul] using
      summable_sum (s := Finset.univ) (fun l _ => hterms l)
  change pairing (fun d => f d + g d) (gaussianCoefficient B) = _
  have hadd : pairing (fun d => f d + g d) (gaussianCoefficient B) =
      pairing f (gaussianCoefficient B) + pairing g (gaussianCoefficient B) := by
    unfold pairing
    simp only [mul_add, add_mul]
    exact hf.tsum_add hg
  rw [hadd]
  congr 1
  · by_cases hij : i = j
    · simp only [f, hij, ite_true]
      simpa only [created_zero] using pairing_created A B 0
    · simp [f, hij, pairing]
  · rw [pairing_comm, pairing_sum_right]
    · simp_rw [pairing_const_right, pairing_comm (gaussianCoefficient B), pairing_created]
    · intro l
      convert hterms l using 1
      funext d
      ring

/-- The genuine second occupation moment satisfies its finite matrix
equation. All infinite rearrangements use absolutely summable native Fock
coefficients, and neither matrix is required to commute with the other. -/
private theorem insertion_second_moment (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) (i j : I) :
    insertion A B (Finsupp.single i 1 + Finsupp.single j 1) =
      B i j * insertion A B 0 +
        ∑ k, ∑ l, B i k * A k l *
          insertion A B (Finsupp.single j 1 + Finsupp.single l 1) := by
  rw [← pairing_created, ← created_add, pairing_creation_annihilation,
    pairing_gaussian_annihilate A B hAsym hBsym hA hB]
  simp_rw [pairing_comm _ (created (Finsupp.single _ 1) (gaussianCoefficient B)),
    pairing_creation_annihilation, pairing_comm (gaussianCoefficient B),
    pairing_annihilate_created A B hAsym hBsym hA hB]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]

private theorem gaussianPiece_particle (A : Matrix I I ℂ) (n : ℕ) :
    (n + 1 : ℂ) • gaussianPiece A (n + 1) = quadratic A * gaussianPiece A n := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hscalar : (n + 1 : ℂ) * ((n + 1).factorial : ℂ)⁻¹ = (n.factorial : ℂ)⁻¹ := by
    rw [hf]
    field_simp
  simp only [gaussianPiece, smul_smul, hscalar, pow_succ', mul_smul_comm]

private theorem quadratic_piece_coeff (A : Matrix I I ℂ) (n : ℕ) (d : I →₀ ℕ)
    (hd : d.degree = 2 * (n + 1)) :
    (quadratic A * gaussianPiece A n).coeff d = (1 / 2 : ℂ) *
      ∑ i, ∑ j, A i j * created (Finsupp.single i 1 + Finsupp.single j 1)
        (gaussianCoefficient A) d := by
  simp only [quadratic, smul_mul_assoc, Finset.sum_mul, coeff_smul, coeff_sum,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hmono : (X i * X j : MvPolynomial I ℂ) =
      monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
    simp only [X, monomial_mul_monomial, one_mul]
  rw [hmono, coeff_monomial_mul']
  by_cases hle : Finsupp.single i 1 + Finsupp.single j 1 ≤ d
  · have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    have hlow : (d - (Finsupp.single i 1 + Finsupp.single j 1)).degree = 2 * n := by
      simp only [map_add, Finsupp.degree_single] at he
      omega
    simp only [created, hle, ite_true, one_mul]
    exact (gaussianCoefficient_even A _ n hlow).symm
  · simp [created, hle]

private theorem coefficient_particle (A : Matrix I I ℂ) (n : ℕ) (d : I →₀ ℕ)
    (hd : d.degree = 2 * (n + 1)) :
    (n + 1 : ℂ) * gaussianCoefficient A d = (1 / 2 : ℂ) *
      ∑ i, ∑ j, A i j * created (Finsupp.single i 1 + Finsupp.single j 1)
        (gaussianCoefficient A) d := by
  have he := congrArg (fun p : MvPolynomial I ℂ => p.coeff d) (gaussianPiece_particle A n)
  simpa only [coeff_smul, smul_eq_mul, ← gaussianCoefficient_even A d (n + 1) hd,
    quadratic_piece_coeff A n d hd] using he

private theorem coefficientDerivative_eq (A : Matrix I I ℂ) (d : I →₀ ℕ) (t : ℂ) :
    (d.degree / 2 : ℕ) * t ^ (d.degree / 2 - 1) * gaussianCoefficient A d =
      (1 / 2 : ℂ) * ∑ i, ∑ j, A i j *
        created (Finsupp.single i 1 + Finsupp.single j 1) (gaussianCoefficient (t • A)) d := by
  by_cases hodd : d.degree % 2 = 1
  · rw [gaussianCoefficient_odd A d hodd, mul_zero]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hle : Finsupp.single i 1 + Finsupp.single j 1 ≤ d
    · have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      simp only [map_add, Finsupp.degree_single] at he
      simp only [created, hle, ite_true]
      rw [gaussianCoefficient_odd _ _ (by omega), mul_zero]
    · simp [created, hle]
  · have heven : d.degree = 2 * (d.degree / 2) := by omega
    generalize hn : d.degree / 2 = n at *
    cases n with
    | zero =>
      have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      subst d
      simp only [Nat.cast_zero, zero_mul, mul_zero]
      symm
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      have hnot : ¬Finsupp.single i 1 + Finsupp.single j 1 ≤ (0 : I →₀ ℕ) := by
        intro h
        have hh := Finsupp.degree_mono h
        simp at hh
      simp [created, hnot]
    | succ n =>
      have hd : d.degree = 2 * (n + 1) := heven
      have hscale (i j : I) :
          created (Finsupp.single i 1 + Finsupp.single j 1) (gaussianCoefficient (t • A)) d =
            t ^ n * created (Finsupp.single i 1 + Finsupp.single j 1)
              (gaussianCoefficient A) d := by
        by_cases hle : Finsupp.single i 1 + Finsupp.single j 1 ≤ d
        · have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
          simp only [map_add, Finsupp.degree_single] at he
          have hlow : (d - (Finsupp.single i 1 + Finsupp.single j 1)).degree = 2 * n := by omega
          simp only [created, hle, ite_true, gaussianCoefficient_smul, hlow,
            Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
        · simp [created, hle]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      calc
        _ = t ^ n * ((n + 1 : ℂ) * gaussianCoefficient A d) := by push_cast; ring
        _ = _ := by
          rw [coefficient_particle A n d hd]
          simp only [hscale, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

private theorem vacuum_derivative_moment (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    {S : ℝ} (hS : 1 < S)
    (hSA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((S : ℂ) • A)‖ < 1)
    {t : ℂ} (ht : ‖t‖ < S)
    (hAt : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (t • A)‖ < 1) :
    HasDerivAt (fun z : ℂ => insertion (z • A) B 0)
      ((1 / 2 : ℂ) * ∑ i, ∑ j, A i j *
        insertion (t • A) B (Finsupp.single i 1 + Finsupp.single j 1)) t := by
  have h := insertion_hasDerivAt A B hAsym hBsym hB hS hSA 0 ht
  have hsym : ∀ i j, (t • A) i j = (t • A) j i := by
    intro i j
    simp only [Matrix.smul_apply]
    rw [hAsym i j]
  have hs (i j : I) : Summable (fun d : I →₀ ℕ => A i j * ((weight d : ℂ) *
      created (Finsupp.single i 1 + Finsupp.single j 1) (gaussianCoefficient (t • A)) d *
        gaussianCoefficient B d)) := by
    simpa only [created_zero] using (created_pair_summable (t • A) B hsym hBsym hAt hB
      (Finsupp.single i 1 + Finsupp.single j 1) 0).mul_left (A i j)
  convert h using 1
  symm
  calc
    _ = (1 / 2 : ℂ) * ∑' d : I →₀ ℕ, ∑ i, ∑ j, A i j * ((weight d : ℂ) *
        created (Finsupp.single i 1 + Finsupp.single j 1) (gaussianCoefficient (t • A)) d *
          gaussianCoefficient B d) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      simp only [insertionDerivativeTerm, add_zero, coefficientDerivative_eq,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (1 / 2 : ℂ) * ∑ i, ∑ j, A i j *
        pairing (created (Finsupp.single i 1 + Finsupp.single j 1)
          (gaussianCoefficient (t • A))) (gaussianCoefficient B) := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
      simp only [pairing, tsum_mul_left]
    _ = _ := by simp only [pairing_created]

open scoped Matrix.Norms.L2Operator

private def secondMoment (A B : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => insertion A B (Finsupp.single i 1 + Finsupp.single j 1)

private theorem secondMoment_solved (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    secondMoment A B = insertion A B 0 • ((1 - B * A)⁻¹ʳ * B) := by
  have hBA : ‖B * A‖ < 1 := (norm_mul_le B A).trans_lt
    ((mul_le_of_le_one_left (norm_nonneg A) hB.le).trans_lt hA)
  have hu := isUnit_one_sub_of_norm_lt_one hBA
  have hrec : secondMoment A B = insertion A B 0 • B + B * A * secondMoment A B := by
    ext i j
    change insertion A B (Finsupp.single i 1 + Finsupp.single j 1) = _
    rw [insertion_second_moment A B hAsym hBsym hA hB i j]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Finset.sum_mul, secondMoment]
    rw [mul_comm (insertion A B 0), Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm (Finsupp.single j 1) (Finsupp.single l 1)]
  have heq : (1 - B * A) * secondMoment A B = insertion A B 0 • B := by
    rw [sub_mul, one_mul]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hrec)
  calc
    _ = (1 - B * A)⁻¹ʳ * ((1 - B * A) * secondMoment A B) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
    _ = _ := by rw [heq, mul_smul_comm]

private def traceCLM : Matrix I I ℂ →L[ℂ] ℂ :=
  (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap

private def logTerm (A B : Matrix I I ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  t ^ (n + 1) * Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)

private def logDerivativeTerm (A B : Matrix I I ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  t ^ n * Matrix.trace ((A * B) ^ (n + 1))

/-- The trace-log series with its branch normalized at the zero scaling. -/
def vacuumTraceLog (A B : Matrix I I ℂ) (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑' n : ℕ, logTerm A B n t

private theorem logTerm_hasDerivAt (A B : Matrix I I ℂ) (n : ℕ) (t : ℂ) :
    HasDerivAt (logTerm A B n) (logDerivativeTerm A B n t) t := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  convert ((hasDerivAt_pow (n + 1) t).mul_const
    (Matrix.trace ((A * B) ^ (n + 1)))).div_const (n + 1 : ℂ) using 1
  · rfl
  · simp only [logDerivativeTerm, Nat.add_sub_cancel]
    field_simp
    push_cast
    ring

private theorem logDerivativeTerm_bound (A B : Matrix I I ℂ) {S : ℝ} (hS : 0 ≤ S)
    (n : ℕ) {t : ℂ} (ht : ‖t‖ ≤ S) :
    ‖logDerivativeTerm A B n t‖ ≤ ‖(traceCLM : Matrix I I ℂ →L[ℂ] ℂ)‖ *
      ‖A * B‖ * (S * ‖A * B‖) ^ n := by
  have htr : ‖Matrix.trace ((A * B) ^ (n + 1))‖ ≤
      ‖(traceCLM : Matrix I I ℂ →L[ℂ] ℂ)‖ * ‖A * B‖ ^ (n + 1) := by
    exact (ContinuousLinearMap.le_opNorm (traceCLM : Matrix I I ℂ →L[ℂ] ℂ) _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_le' _ (Nat.succ_pos n)) (norm_nonneg _))
  simp only [logDerivativeTerm, norm_mul, norm_pow]
  calc
    _ ≤ S ^ n * (‖(traceCLM : Matrix I I ℂ →L[ℂ] ℂ)‖ * ‖A * B‖ ^ (n + 1)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht n) htr (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow, pow_succ]; ring

private theorem logSeries_hasDerivAt (A B : Matrix I I ℂ) {S : ℝ} (hS : 0 < S)
    (hAB : S * ‖A * B‖ < 1) {t : ℂ} (ht : ‖t‖ < S) :
    HasDerivAt (vacuumTraceLog A B)
      ((1 / 2 : ℂ) * ∑' n : ℕ, logDerivativeTerm A B n t) t := by
  have hu := (summable_geometric_of_lt_one (mul_nonneg hS.le (norm_nonneg (A * B))) hAB).mul_left
    (‖(traceCLM : Matrix I I ℂ →L[ℂ] ℂ)‖ * ‖A * B‖)
  exact (hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) S).isPreconnected
    (fun n z _ => logTerm_hasDerivAt A B n z)
    (fun n z hz => logDerivativeTerm_bound A B hS.le n
      (by
        have hh : ‖z‖ < S := by simpa using hz
        exact hh.le))
    (y₀ := (0 : ℂ)) (by simpa using hS)
    (by simpa [logTerm] using (summable_zero : Summable (fun _ : ℕ => (0 : ℂ))))
    (by simpa using ht)).const_mul (1 / 2 : ℂ)

private theorem sandwich_power (A B : Matrix I I ℂ) (n : ℕ) :
    A * (B * A) ^ n * B = (A * B) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (A * (B * A) ^ n * B) * (A * B) := by rw [pow_succ]; noncomm_ring
      _ = _ := by rw [ih]; exact (pow_succ (A * B) (n + 1)).symm

private theorem trace_geometric_inverse (A B : Matrix I I ℂ) {t : ℂ}
    (hBA : ‖t • (B * A)‖ < 1) :
    (∑' n : ℕ, logDerivativeTerm A B n t) =
      Matrix.trace (A * (1 - t • (B * A))⁻¹ʳ * B) := by
  let F : Matrix I I ℂ →L[ℂ] ℂ :=
    ({ toFun := fun X => Matrix.trace (A * X * B)
       map_add' := by intro X Y; simp [mul_add, add_mul, Matrix.trace_add]
       map_smul' := by intro c X; simp [mul_smul_comm, smul_mul_assoc, Matrix.trace_smul]
     } : Matrix I I ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hs := summable_geometric_of_norm_lt_one hBA
  calc
    _ = ∑' n : ℕ, F ((t • (B * A)) ^ n) := by
      apply tsum_congr
      intro n
      simp only [F, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
        AddHom.coe_mk, smul_pow, mul_smul_comm, smul_mul_assoc, Matrix.trace_smul,
        sandwich_power, smul_eq_mul, logDerivativeTerm]
    _ = F (∑' n : ℕ, (t • (B * A)) ^ n) := (F.map_tsum hs).symm
    _ = _ := by rw [geom_series_eq_inverse _ hBA]; rfl

private theorem logSeries_summable (A B : Matrix I I ℂ) {S : ℝ} (hS : 0 < S)
    (hAB : S * ‖A * B‖ < 1) {t : ℂ} (ht : ‖t‖ < S) :
    Summable (fun n : ℕ => logTerm A B n t) := by
  have hu := (summable_geometric_of_lt_one (mul_nonneg hS.le (norm_nonneg (A * B))) hAB).mul_left
    (‖(traceCLM : Matrix I I ℂ →L[ℂ] ℂ)‖ * ‖A * B‖)
  exact summable_of_summable_hasDerivAt_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) S).isPreconnected
    (fun n z _ => logTerm_hasDerivAt A B n z)
    (fun n z hz => logDerivativeTerm_bound A B hS.le n
      (by
        have hh : ‖z‖ < S := by simpa using hz
        exact hh.le))
    (y₀ := (0 : ℂ)) (by simpa using hS)
    (by simpa [logTerm] using (summable_zero : Summable (fun _ : ℕ => (0 : ℂ))))
    (by simpa using ht)

private theorem scaled_strict (A : Matrix I I ℂ) {S : ℝ} (hS : 0 ≤ S)
    (hSA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((S : ℂ) • A)‖ < 1)
    {t : ℂ} (ht : ‖t‖ ≤ S) : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (t • A)‖ < 1 := by
  rw [map_smul, norm_smul] at hSA ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS] at hSA
  exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_lt hSA

private theorem vacuum_hasDerivAt (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    {S : ℝ} (hS : 1 < S)
    (hSA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((S : ℂ) • A)‖ < 1)
    {t : ℂ} (ht : ‖t‖ < S) :
    HasDerivAt (fun z : ℂ => insertion (z • A) B 0)
      (((1 / 2 : ℂ) * Matrix.trace (A * (1 - t • (B * A))⁻¹ʳ * B)) *
        insertion (t • A) B 0) t := by
  have hAt := scaled_strict A (zero_lt_one.trans hS).le hSA ht.le
  have hsym : ∀ i j, (t • A) i j = (t • A) j i := by
    intro i j
    simp only [Matrix.smul_apply]
    rw [hAsym i j]
  have hsol := secondMoment_solved (t • A) B hsym hBsym hAt hB
  have htrace : (∑ i, ∑ j, A i j *
      insertion (t • A) B (Finsupp.single i 1 + Finsupp.single j 1)) =
        Matrix.trace (A * secondMoment (t • A) B) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, secondMoment]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [add_comm (Finsupp.single i 1) (Finsupp.single j 1)]
  convert vacuum_derivative_moment A B hAsym hBsym hB hS hSA ht hAt using 1
  rw [htrace, hsol, mul_smul_comm, Matrix.trace_smul]
  simp only [smul_eq_mul, mul_smul_comm]
  rw [← mul_assoc A]
  ring

private theorem gaussianCoefficient_zero_matrix (d : I →₀ ℕ) :
    gaussianCoefficient (0 : Matrix I I ℂ) d = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst d
    simp [gaussianCoefficient_zero]
  · by_cases hn : d.degree / 2 = 0
    · simp [gaussianCoefficient, hn, gaussianPiece, MvPolynomial.coeff_one, hd, eq_comm]
    · have hq : quadratic (0 : Matrix I I ℂ) = 0 := by simp [quadratic]
      simp [gaussianCoefficient, gaussianPiece, hq, hn, hd]

private theorem vacuum_zero (B : Matrix I I ℂ) : insertion 0 B 0 = 1 := by
  simp [insertion, gaussianCoefficient_zero_matrix, gaussianCoefficient_zero,
    mul_ite, ite_mul, weight]

/-- The normalized trace-log exponential equals the actual unconditional
bilinear occupation vacuum. The mode type may be empty; A and B are complex
symmetric strict contractions, with no commutativity or positivity premise. -/
theorem vacuum_trace_log (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    Summable (fun d : I →₀ ℕ =>
      ‖(weight d : ℂ) * gaussianCoefficient A d * gaussianCoefficient B d‖) ∧
    Summable (fun n : ℕ => Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) ∧
      (∑' d : I →₀ ℕ, (weight d : ℂ) * gaussianCoefficient A d * gaussianCoefficient B d) =
        Complex.exp ((1 / 2 : ℂ) *
          ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) := by
  let a : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
  let S : ℝ := 2 / (1 + a)
  have ha : 0 ≤ a := norm_nonneg _
  have hden : 0 < 1 + a := by positivity
  have hS : 1 < S := (lt_div_iff₀ hden).2 (by dsimp [a]; linarith)
  have hS0 : 0 < S := zero_lt_one.trans hS
  have hSa : S * a < 1 := by
    dsimp [S]
    rw [div_mul_eq_mul_div, div_lt_one hden]
    dsimp [a]
    linarith
  have hSA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((S : ℂ) • A)‖ < 1 := by
    simpa only [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hS0] using hSa
  have hAB : S * ‖A * B‖ < 1 := by
    calc
      _ ≤ S * (‖A‖ * ‖B‖) := mul_le_mul_of_nonneg_left (norm_mul_le A B) hS0.le
      _ ≤ S * ‖A‖ := by
        have hh : ‖B‖ ≤ (1 : ℝ) := hB.le
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (norm_nonneg A) hh) hS0.le
      _ < 1 := hSa
  have hlog (t : ℂ) (ht : ‖t‖ < S) :
      HasDerivAt (vacuumTraceLog A B)
        ((1 / 2 : ℂ) * Matrix.trace (A * (1 - t • (B * A))⁻¹ʳ * B)) t := by
    have hAt := scaled_strict A hS0.le hSA ht.le
    have hBA : ‖t • (B * A)‖ < 1 := by
      rw [← mul_smul_comm]
      exact (norm_mul_le B (t • A)).trans_lt ((mul_le_of_le_one_left (norm_nonneg (t • A)) hB.le).trans_lt hAt)
    simpa only [trace_geometric_inverse A B hBA] using logSeries_hasDerivAt A B hS0 hAB ht
  let F : ℂ → ℂ := fun t => insertion (t • A) B 0 * Complex.exp (-vacuumTraceLog A B t)
  have hF (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) S) : HasDerivAt F 0 t := by
    have hnorm : ‖t‖ < S := by simpa using ht
    have hZ := vacuum_hasDerivAt A B hAsym hBsym hB hS hSA hnorm
    have hL := hlog t hnorm
    convert hZ.mul hL.neg.cexp using 1 <;> first | rfl | ring
  have hconst : F 1 = F 0 := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) S).isPreconnected
    (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hF t ht).deriv)
    (by simpa using hS) (by simpa using hS0)
  have heq : insertion A B 0 * Complex.exp (-vacuumTraceLog A B 1) = 1 := by
    simpa [F, vacuumTraceLog, logTerm, vacuum_zero] using hconst
  have hfinal := congrArg (fun z : ℂ => z * Complex.exp (vacuumTraceLog A B 1)) heq
  have hcancel : Complex.exp (-vacuumTraceLog A B 1) * Complex.exp (vacuumTraceLog A B 1) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [mul_assoc, hcancel, mul_one, one_mul] at hfinal
  refine ⟨?_, ?_, ?_⟩
  · simpa only [add_zero] using insertion_norm_summable A B hAsym hBsym hA hB 0
  · simpa [logTerm] using logSeries_summable A B hS0 hAB (t := 1) (by simpa using hS)
  · simpa [insertion, vacuumTraceLog, logTerm] using hfinal

end D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
