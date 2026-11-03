/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicJointHolomorphy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicJointHolomorphy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded lp 1 by lp 1 convolution is constructed directly into the original lp 2 space and evaluated by its finite antidiagonal coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicHilbertHolomorphy
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
This is the joint endpoint of the original cubic analytic chain. Native
verification receipts and independent admission are recorded separately.

The outputs in this file are the existing eSeries, pSeries and qSeries.
Their definitions are not changed. The carrier is OriginalGaussianResolvent.H
= lp (fun _ : Nat => Complex) 2. In particular eValue is
  z^(n+1) * currentRow b root (n+1) / sqrt(n+1),
where currentRow is the literal finite sum in OriginalGaussianCubicKernel.
The existing p/q series are supported expansions of the actual TT/UT contour
coefficients, rather than definitions by an inverse operator.

The auxiliary lp 1 carrier is used only to construct a bounded bilinear map
into that unchanged Hilbert space. Its coordinate equality is proved before
it is used to establish joint analyticity. No root existence, joint
holomorphy, normal convergence or coefficient correspondence is a new premise.
The final p/q transfer uses the original proved supplier
original_extensions_correspondence, on a proved neighborhood of the original
domain and root equation. mixedOperator is the original negative Neumann sum,
including its degree-zero -I term.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicJointHolomorphy

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianCubicKernel
open OriginalGaussianCubicAnalytic OriginalGaussianCubicHilbertHolomorphy

private abbrev V := OriginalGaussianResolvent.H
private abbrev Op := V →L[ℂ] V

/-- An auxiliary summable-sequence space, not a replacement output carrier. -/
abbrev L := lp (fun _ : ℕ => ℂ) 1

private lemma L_summable (u : L) : Summable (fun i : ℕ => ‖u i‖) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    u.property.summable (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)

private lemma L_norm (u : L) : ‖u‖ = ∑' i : ℕ, ‖u i‖ := by
  simpa using lp.norm_eq_tsum_rpow
    (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal) u

private lemma norm_nat_succ (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)

/-- The (0,0) term has no positive original output mode. -/
def K (i j : ℕ) : V :=
  if i + j = 0 then 0 else
    lp.single 2 (i + j - 1)
      ((Real.sqrt (i + j : ℝ) : ℂ) /
        (((i + 1 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ)))

private lemma K_norm (i j : ℕ) : ‖K i j‖ ≤ 1 := by
  by_cases h : i + j = 0
  · simp [K, h]
  · have hd : (0 : ℝ) < (i + 1 : ℝ) * (j + 1 : ℝ) := by positivity
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hs : Real.sqrt (i + j : ℝ) ≤ (i + 1 : ℝ) * (j + 1 : ℝ) := by
      calc
        _ ≤ (i + j : ℝ) + 1 := by
          apply (Real.sqrt_le_iff).2
          constructor
          · positivity
          · nlinarith [sq_nonneg (i + j : ℝ)]
        _ ≤ _ := by nlinarith [mul_nonneg hi hj]
    rw [K, if_neg h, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
      norm_div, norm_mul]
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_natCast,
      Nat.cast_add, Nat.cast_one, norm_nat_succ] using (div_le_one hd).2 hs

private def convolutionTerm (u v : L) (ij : ℕ × ℕ) : V :=
  (u ij.1 * v ij.2) • K ij.1 ij.2

private lemma convolutionTerm_bound (u v : L) (ij : ℕ × ℕ) :
    ‖convolutionTerm u v ij‖ ≤ ‖u ij.1‖ * ‖v ij.2‖ := by
  rw [convolutionTerm, norm_smul, norm_mul]
  exact mul_le_of_le_one_right (by positivity) (K_norm _ _)

private lemma convolution_summable (u v : L) :
    Summable (convolutionTerm u v) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (convolutionTerm_bound u v)
    ((L_summable u).mul_of_nonneg (L_summable v)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))

private def convolutionSum (u v : L) : V := ∑' ij : ℕ × ℕ, convolutionTerm u v ij

private lemma convolutionSum_bound (u v : L) :
    ‖convolutionSum u v‖ ≤ ‖u‖ * ‖v‖ := by
  have hm := (L_summable u).mul_of_nonneg (L_summable v)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  calc
    _ ≤ ∑' ij : ℕ × ℕ, ‖u ij.1‖ * ‖v ij.2‖ :=
      tsum_of_norm_bounded hm.hasSum (convolutionTerm_bound u v)
    _ = (∑' i : ℕ, ‖u i‖) * ∑' j : ℕ, ‖v j‖ := by
      rw [hm.tsum_prod]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
    _ = _ := by rw [← L_norm u, ← L_norm v]

private def convolutionLinear : L →ₗ[ℂ] L →ₗ[ℂ] V :=
  LinearMap.mk₂ ℂ convolutionSum
    (by
      intro u v w
      unfold convolutionSum
      simp only [convolutionTerm, lp.coeFn_add, Pi.add_apply, add_mul, add_smul]
      exact (convolution_summable u w).tsum_add (convolution_summable v w))
    (by
      intro c u v
      change (∑' ij : ℕ × ℕ, convolutionTerm (c • u) v ij) =
        c • ∑' ij : ℕ × ℕ, convolutionTerm u v ij
      calc
        _ = ∑' ij : ℕ × ℕ, c • convolutionTerm u v ij := by
          apply tsum_congr
          intro ij
          simp [convolutionTerm, mul_assoc, mul_smul]
        _ = _ := Summable.tsum_const_smul c (convolution_summable u v))
    (by
      intro u v w
      unfold convolutionSum
      simp only [convolutionTerm, lp.coeFn_add, Pi.add_apply, mul_add, add_smul]
      exact (convolution_summable u v).tsum_add (convolution_summable u w))
    (by
      intro c u v
      change (∑' ij : ℕ × ℕ, convolutionTerm u (c • v) ij) =
        c • ∑' ij : ℕ × ℕ, convolutionTerm u v ij
      calc
        _ = ∑' ij : ℕ × ℕ, c • convolutionTerm u v ij := by
          apply tsum_congr
          intro ij
          simp [convolutionTerm, mul_left_comm, mul_assoc, mul_smul]
        _ = _ := Summable.tsum_const_smul c (convolution_summable u v))

/-- The actual bounded bilinear convolution into the original Hilbert carrier. -/
def C : L →L[ℂ] L →L[ℂ] V :=
  convolutionLinear.mkContinuous₂ 1 (by
    intro u v
    change ‖convolutionSum u v‖ ≤ 1 * ‖u‖ * ‖v‖
    simpa only [one_mul] using convolutionSum_bound u v)

/-- Evaluation of the absolutely convergent convolution is a finite
antidiagonal sum. This includes n=0, hence the pairs (0,1) and (1,0). -/
theorem C_coordinate (u v : L) (n : ℕ) :
    C u v n = (Real.sqrt (n + 1 : ℝ) : ℂ) *
      ∑ i ∈ Finset.range (n + 1 + 1),
        u i * v (n + 1 - i) /
          (((i + 1 : ℕ) : ℂ) * ((n + 1 - i + 1 : ℕ) : ℂ)) := by
  classical
  let E := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n
  change E (∑' ij : ℕ × ℕ, convolutionTerm u v ij) = _
  rw [E.map_tsum (convolution_summable u v)]
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), E (convolutionTerm u v ij) := by
      apply tsum_eq_sum
      intro ij hij
      have hsum : ij.1 + ij.2 ≠ n + 1 := by
        simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hij
      by_cases hzero : ij.1 + ij.2 = 0
      · simp [convolutionTerm, K, hzero]
      · have hidx : ij.1 + ij.2 - 1 ≠ n := by omega
        change ((u ij.1 * v ij.2) • K ij.1 ij.2) n = 0
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        rw [K, if_neg hzero, lp.single_apply_ne 2 _ _ (Ne.symm hidx), mul_zero]
    _ = _ := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ n + 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hsum : i + (n + 1 - i) = n + 1 := Nat.add_sub_of_le hi'
      have hsumR : (i : ℝ) + ((n + 1 - i : ℕ) : ℝ) = (n + 1 : ℝ) := by
        exact_mod_cast hsum
      have hidx : i + (n + 1 - i) - 1 = n := by omega
      simp [E, convolutionTerm, K, hsum, hsumR, hidx, smul_eq_mul,
        lp.evalCLM, lp.single_apply_self]
      ring

private lemma half_norm (n : ℕ) : ‖halfBinomial n‖ ≤ 1 := by
  rw [halfBinomial_eq_signed_centralWeight, norm_mul, norm_pow]
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (centralWeight_nonneg n)] using weight_le_one n

private lemma choose_half_bound (n : ℕ) : ‖Ring.choose (1 / 2 : ℂ) n‖ ≤ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have he : Ring.choose (1 / 2 : ℂ) (n + 1) =
          halfBinomial n + halfBinomial (n + 1) := by
        rw [halfBinomial_choose, halfBinomial_choose, ← Ring.choose_succ_succ]
        congr 1
        ring
      rw [he]
      exact (norm_add_le _ _).trans (by linarith [half_norm n, half_norm (n + 1)])

private def familyCoefficient (binomial : Bool) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) * (if binomial then Ring.choose (1 / 2 : ℂ) n else 1)

private def familyTerm (binomial : Bool) (t : ℂ) (n : ℕ) : L :=
  lp.single 1 n (familyCoefficient binomial n * t ^ n)

private def family (binomial : Bool) (t : ℂ) : L := ∑' n : ℕ, familyTerm binomial t n

/-- a_i(t) = (i+1) choose(1/2,i) t^i in the genuine lp 1 space. -/
def a (t : ℂ) : L := family true t

/-- g_j(t) = (j+1) t^j in the genuine lp 1 space. -/
def g (t : ℂ) : L := family false t

private lemma familyTerm_bound (binomial : Bool) {t : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ht : ‖t‖ ≤ R) (n : ℕ) :
    ‖familyTerm binomial t n‖ ≤ 2 * (n + 1 : ℝ) * R ^ n := by
  have hc : ‖familyCoefficient binomial n‖ ≤ 2 * (n + 1 : ℝ) := by
    cases binomial with
    | false =>
        change ‖((n + 1 : ℕ) : ℂ) * 1‖ ≤ 2 * (n + 1 : ℝ)
        simp only [mul_one, Complex.norm_natCast, Nat.cast_add, Nat.cast_one,
          norm_nat_succ]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    | true =>
        change ‖((n + 1 : ℕ) : ℂ) * Ring.choose (1 / 2 : ℂ) n‖ ≤ _
        rw [norm_mul, Complex.norm_natCast]
        calc
          _ ≤ ((n + 1 : ℕ) : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left (choose_half_bound n) (by positivity)
          _ = _ := by push_cast; ring
  rw [familyTerm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_mul, norm_pow]
  exact mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg _) ht n)
    (pow_nonneg (norm_nonneg _) _) (by positivity)

private lemma family_majorant {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    Summable (fun n : ℕ => 2 * (n + 1 : ℝ) * R ^ n) := by
  have hnorm : ‖R‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hR] using hR1
  have h := ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).add
    (summable_geometric_of_lt_one hR hR1)).mul_left 2
  convert h using 1
  funext n
  simp only [pow_one]
  ring

private lemma family_summable (binomial : Bool) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable (familyTerm binomial t) := by
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (familyTerm_bound binomial (norm_nonneg t) le_rfl)
    (family_majorant (norm_nonneg t) ht)).of_norm

private lemma family_coordinate (binomial : Bool) {t : ℂ} (ht : ‖t‖ < 1) (n : ℕ) :
    family binomial t n = familyCoefficient binomial n * t ^ n := by
  let E := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 n
  change E (∑' i : ℕ, familyTerm binomial t i) = _
  rw [E.map_tsum (family_summable binomial ht)]
  calc
    _ = E (familyTerm binomial t n) := by
      apply tsum_eq_single n
      intro i hi
      exact lp.single_apply_ne 1 i _ (Ne.symm hi)
    _ = _ := lp.single_apply_self 1 n _

private lemma family_analytic (binomial : Bool) {t : ℂ} (ht : ‖t‖ < 1) :
    AnalyticAt ℂ (family binomial) t := by
  have hd : DifferentiableOn ℂ (family binomial) (ball 0 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    obtain ⟨R, hwR, hR1⟩ := exists_between hw1
    have hR : 0 < R := (norm_nonneg w).trans_lt hwR
    have hterm (n : ℕ) : DifferentiableOn ℂ
        (fun z : ℂ => familyTerm binomial z n) (ball 0 R) := by
      intro z _
      have hs : DifferentiableAt ℂ (fun z : ℂ => familyCoefficient binomial n * z ^ n) z :=
        (differentiableAt_const _).mul (differentiableAt_id.pow n)
      exact ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 n).differentiableAt.comp
        z hs).differentiableWithinAt
    have hsum := Complex.differentiableOn_tsum_of_summable_norm
      (family_majorant hR.le hR1) hterm isOpen_ball
      (fun n z hz => familyTerm_bound binomial hR.le
        (le_of_lt (by simpa using hz)) n)
    exact (hsum.differentiableAt
      (isOpen_ball.mem_nhds (by simpa using hwR))).differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa using ht))

private lemma sqrt_index_sq (s : ℕ) :
    (Real.sqrt (s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg s)

private lemma sqrt_index_ne_zero (s : ℕ) (hs : 0 < s) :
    (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hs)).ne'

private lemma factor_term {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hz : ‖z‖ < 1) (hzb : ‖z / b‖ < 1) (s i : ℕ) (hs : 0 < s) (hi : i ≤ s) :
    z ^ s * ((s : ℂ) * root *
      (Ring.choose (1 / 2 : ℂ) i * b ^ i / b ^ (s + 1))) /
        (Real.sqrt (s : ℝ) : ℂ) =
      (root / b) * (Real.sqrt (s : ℝ) : ℂ) *
        (a z i * g (z / b) (s - i) /
          (((i + 1 : ℕ) : ℂ) * ((s - i + 1 : ℕ) : ℂ))) := by
  have hi0 : ((i + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  have hj0 : ((s - i + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s - i)
  have hpz : z ^ s = z ^ i * z ^ (s - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  have hpb : b ^ (s + 1) = b ^ (s - i) * b ^ i * b := by
    rw [← pow_add, Nat.sub_add_cancel hi, ← pow_succ]
  change _ = (root / b) * (Real.sqrt (s : ℝ) : ℂ) *
    (family true z i * family false (z / b) (s - i) / _)
  rw [family_coordinate true hz, family_coordinate false hzb]
  simp only [familyCoefficient, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hpz, hpb, div_pow, ← sqrt_index_sq s]
  field_simp [hb, hi0, hj0, sqrt_index_ne_zero s hs]
  <;> ring

/-- Exact equality with the ORIGINAL eSeries on its original disk. No root
equation is needed for e. The endpoint i=s and z=0 are included. For n=0
the two antidiagonal terms give root*z*(1/b^2 + 1/(2*b)). No step divides
by z or drops the endpoint i=s. -/
theorem eSeries_factorization {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hz : ‖z‖ < beta b) :
    eSeries b root z = (root / b) • C (a z) (g (z / b)) := by
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_left _ _)
  have hzb : ‖z / b‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hb)).2 (hz.trans_le (min_le_right _ _))
  ext n
  rw [(external_row_analytic root hz).2 n]
  change eValue b root z n = (root / b) * C (a z) (g (z / b)) n
  rw [C_coordinate]
  calc
    _ = ∑ i ∈ Finset.range (n + 1 + 1),
        z ^ (n + 1) * (((n + 1 : ℕ) : ℂ) * root *
          (Ring.choose (1 / 2 : ℂ) i * b ^ i / b ^ (n + 1 + 1))) /
            (Real.sqrt (n + 1 : ℝ) : ℂ) := by
      simp only [eValue, currentRow, Finset.mul_sum, Finset.sum_div]
    _ = ∑ i ∈ Finset.range (n + 1 + 1),
        (root / b) * (Real.sqrt (n + 1 : ℝ) : ℂ) *
          (a z i * g (z / b) (n + 1 - i) /
            (((i + 1 : ℕ) : ℂ) * ((n + 1 - i + 1 : ℕ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Nat.cast_add, Nat.cast_one] using
        factor_term hb root hz1 hzb (n + 1) i (by omega)
          (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

private lemma original_domain_eventually {b z : ℂ} (hb : b ≠ 0)
    (hz : ‖z‖ < beta b) :
    ∀ᶠ w : ℂ × ℂ in 𝓝 (b, z), w.1 ≠ 0 ∧ ‖w.2‖ < beta w.1 := by
  have hopen : IsOpen {w : ℂ × ℂ | w.1 ≠ 0 ∧ ‖w.2‖ < beta w.1} := by
    apply IsOpen.inter
    · exact isOpen_ne.preimage continuous_fst
    · exact isOpen_lt continuous_snd.norm (continuous_const.min continuous_fst.norm)
  exact hopen.mem_nhds ⟨hb, hz⟩

private lemma eSeries_joint_graph {b z : ℂ} {r : ℂ → ℂ} (hb : b ≠ 0)
    (hr : AnalyticAt ℂ r b) (hz : ‖z‖ < beta b) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => eSeries w.1 (r w.1) w.2) (b, z) := by
  have hbA : AnalyticAt ℂ (fun w : ℂ × ℂ => w.1) (b, z) := analyticAt_fst
  have hzA : AnalyticAt ℂ (fun w : ℂ × ℂ => w.2) (b, z) := analyticAt_snd
  have hrA := hr.comp hbA
  have hquot : AnalyticAt ℂ (fun w : ℂ × ℂ => w.2 / w.1) (b, z) := hzA.div hbA hb
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_left _ _)
  have hzb : ‖z / b‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hb)).2 (hz.trans_le (min_le_right _ _))
  have ha : AnalyticAt ℂ a z := family_analytic true hz1
  have hg : AnalyticAt ℂ g (z / b) := family_analytic false hzb
  have ha' : AnalyticAt ℂ (fun w : ℂ × ℂ => a w.2) (b, z) :=
    ha.comp (f := fun w : ℂ × ℂ => w.2) hzA
  have hg' : AnalyticAt ℂ (fun w : ℂ × ℂ => g (w.2 / w.1)) (b, z) :=
    hg.comp (f := fun w : ℂ × ℂ => w.2 / w.1) hquot
  have hC : AnalyticAt ℂ (fun w : ℂ × ℂ => C (a w.2) (g (w.2 / w.1))) (b, z) :=
    (C.analyticAt_bilinear (a z, g (z / b))).comp₂ ha' hg'
  apply ((hrA.div hbA hb).smul hC).congr
  filter_upwards [original_domain_eventually hb hz] with w hw
  exact (eSeries_factorization hw.1 (r w.1) hw.2).symm

/- These private operator steps have a single live consumer below. They reuse
the original norm derivative and identify the actual square Neumann sum. -/
private lemma operator_analytic {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ operator z := by
  have hd : DifferentiableOn ℂ operator (ball 0 1) := by
    intro w hw
    exact (OriginalGaussianDifferentiation.hasDerivAt_operator
      (by simpa using hw)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa using hz))

private lemma square_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    ‖operator z ^ 2‖ < 1 :=
  (norm_pow_le _ _).trans_lt
    (pow_lt_one₀ (norm_nonneg _) (OriginalGaussianWeightedResolvent.operator_norm_lt_one hz)
      (by norm_num : (2 : ℕ) ≠ 0))

private lemma squareResolvent_eq_inverse {z : ℂ} (hz : ‖z‖ < 1) :
    squareResolvent z = Ring.inverse (1 - operator z ^ 2) := by
  exact (NormedRing.inverse_one_sub (operator z ^ 2) (square_norm_lt_one hz)).symm

private lemma blocks_analytic {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ selfOperator z ∧ AnalyticAt ℂ mixedOperator z := by
  let u : Opˣ := Units.oneSub (operator z ^ 2) (square_norm_lt_one hz)
  have hu : (u : Op) = 1 - operator z ^ 2 := Units.val_oneSub _ _
  have hI : AnalyticAt ℂ (Ring.inverse : Op → Op) (1 - operator z ^ 2) := by
    rw [← hu]
    exact analyticAt_inverse (𝕜 := ℂ) u
  have hR : AnalyticAt ℂ squareResolvent z := by
    have harg : AnalyticAt ℂ (fun w : ℂ => 1 - operator w ^ 2) z :=
      analyticAt_const.sub ((operator_analytic hz).pow 2)
    apply (hI.comp (f := fun w : ℂ => 1 - operator w ^ 2) harg).congr
    have hU : ∀ᶠ w : ℂ in 𝓝 z, ‖w‖ < 1 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hz
    filter_upwards [hU] with w hw
    exact (squareResolvent_eq_inverse hw).symm
  exact ⟨(operator_analytic hz).mul hR, hR.neg⟩

/- The scalar H here is the ORIGINAL convergent (-1/2)-binomial series.
Its private source theorem is restated by proof, not postulated or imported
under an invented public name. -/
private lemma originalH_powerSeries :
    HasFPowerSeriesOnBall OriginalGaussianCubicAnalytic.H
      (binomialSeries ℂ (-1 / 2 : ℂ)) 0 1 := by
  apply Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.congr
  intro v hv
  have hs := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
    (a := (-1 / 2 : ℂ))).hasSum hv
  have he : HasSum (fun n : ℕ => halfBinomial n * v ^ n)
      ((1 + v) ^ (-1 / 2 : ℂ)) := by
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, zero_add, halfBinomial_choose] using hs
  exact he.tsum_eq.symm

private lemma originalH_eq_cpow {v : ℂ} (hv : ‖v‖ < 1) :
    OriginalGaussianCubicAnalytic.H v = (1 + v) ^ (-1 / 2 : ℂ) := by
  have hmem : v ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [edist_dist, dist_eq_norm, ← ofReal_norm, ENNReal.ofReal_lt_one] using hv
  have hs := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
    (a := (-1 / 2 : ℂ))).hasSum hmem
  have he : HasSum (fun n : ℕ => halfBinomial n * v ^ n)
      ((1 + v) ^ (-1 / 2 : ℂ)) := by
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, zero_add, halfBinomial_choose] using hs
  exact he.tsum_eq

private lemma originalH_root {v : ℂ} (hv : ‖v‖ < 1) :
    (1 + v) * OriginalGaussianCubicAnalytic.H v ^ 2 = 1 := by
  have hne : 1 + v ≠ 0 := by
    intro he
    have he' : v = -1 := by linear_combination he
    rw [he'] at hv
    norm_num at hv
  rw [originalH_eq_cpow hv, ← Complex.cpow_mul_nat,
    show (-1 / 2 : ℂ) * (2 : ℕ) = -1 by norm_num, Complex.cpow_neg_one]
  exact mul_inv_cancel₀ hne

/-- A concrete local root graph through the specified root, with no branch
selection restriction on root0. Negating root0 negates this same graph. -/
def rootGraph (b0 root0 b : ℂ) : ℂ :=
  root0 * OriginalGaussianCubicAnalytic.H ((b - b0) / (1 + b0))

private lemma one_add_ne_zero {b0 root0 : ℂ}
    (hroot : (1 + b0) * root0 ^ 2 = 1) : 1 + b0 ≠ 0 := by
  intro h
  rw [h, zero_mul] at hroot
  exact zero_ne_one hroot

private lemma rootGraph_equation {b0 root0 b : ℂ}
    (hroot : (1 + b0) * root0 ^ 2 = 1)
    (hb : ‖(b - b0) / (1 + b0)‖ < 1) :
    (1 + b) * rootGraph b0 root0 b ^ 2 = 1 := by
  have hne := one_add_ne_zero hroot
  have hfactor : 1 + b = (1 + b0) * (1 + (b - b0) / (1 + b0)) := by
    field_simp [hne]
    <;> ring
  calc
    _ = ((1 + b0) * root0 ^ 2) *
        ((1 + (b - b0) / (1 + b0)) *
          OriginalGaussianCubicAnalytic.H ((b - b0) / (1 + b0)) ^ 2) := by
      rw [hfactor]
      dsimp only [rootGraph]
      ring
    _ = 1 := by rw [hroot, originalH_root hb, one_mul]

/-- The graph is constructed and proved analytic and root-valued locally.
Existence of this graph is a conclusion, not an input to the joint theorem. -/
theorem rootGraph_spec {b0 root0 : ℂ} (hroot : (1 + b0) * root0 ^ 2 = 1) :
    rootGraph b0 root0 b0 = root0 ∧
      AnalyticAt ℂ (rootGraph b0 root0) b0 ∧
        ∀ᶠ b : ℂ in 𝓝 b0, (1 + b) * rootGraph b0 root0 b ^ 2 = 1 := by
  have hne := one_add_ne_zero hroot
  have hH : AnalyticAt ℂ OriginalGaussianCubicAnalytic.H 0 :=
    originalH_powerSeries.analyticAt_of_mem (by simp)
  have harg : AnalyticAt ℂ (fun b : ℂ => (b - b0) / (1 + b0)) b0 :=
    (analyticAt_id.sub analyticAt_const).div analyticAt_const hne
  have hgraph : AnalyticAt ℂ (rootGraph b0 root0) b0 := by
    have hcomp := hH.comp_of_eq harg (by simp)
    exact analyticAt_const.mul hcomp
  have hsmall : ∀ᶠ b : ℂ in 𝓝 b0, ‖(b - b0) / (1 + b0)‖ < 1 := by
    have hopen : IsOpen {b : ℂ | ‖(b - b0) / (1 + b0)‖ < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    exact hopen.mem_nhds (by simp)
  refine ⟨?_, hgraph, ?_⟩
  · have hH0 : OriginalGaussianCubicAnalytic.H 0 = 1 := by
      rw [originalH_eq_cpow (by norm_num : ‖(0 : ℂ)‖ < 1)]
      simp
    simp only [rootGraph, sub_self, zero_div, hH0, mul_one]
  · filter_upwards [hsmall] with b hb
    exact rootGraph_equation hroot hb

/-- Genuine joint analyticity over Complex x Complex, with unchanged lp 2
outputs, on the full original domain. It includes z0=0 and either root.
The eventual equality used for p/q is confined to the strict original
domain and the actual root equation. -/
theorem original_joint_hilbert_analytic {b0 root0 z0 : ℂ} (hb : b0 ≠ 0)
    (hroot : (1 + b0) * root0 ^ 2 = 1) (hz : ‖z0‖ < beta b0) :
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => eSeries w.1 (rootGraph b0 root0 w.1) w.2) (b0, z0) ∧
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => pSeries w.1 (rootGraph b0 root0 w.1) w.2) (b0, z0) ∧
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => qSeries w.1 (rootGraph b0 root0 w.1) w.2) (b0, z0) := by
  have hspec := rootGraph_spec hroot
  have hE := eSeries_joint_graph hb hspec.2.1 hz
  have hz1 : ‖z0‖ < 1 := hz.trans_le (min_le_left _ _)
  obtain ⟨hself, hmixed⟩ := blocks_analytic (z := z0) hz1
  have hself' : AnalyticAt ℂ (fun w : ℂ × ℂ => selfOperator w.2) (b0, z0) := by
    exact AnalyticAt.comp (𝕜 := ℂ) (g := selfOperator)
      (f := fun w : ℂ × ℂ => w.2) (x := (b0, z0)) hself analyticAt_snd
  have hmixed' : AnalyticAt ℂ (fun w : ℂ × ℂ => mixedOperator w.2) (b0, z0) := by
    exact AnalyticAt.comp (𝕜 := ℂ) (g := mixedOperator)
      (f := fun w : ℂ × ℂ => w.2) (x := (b0, z0)) hmixed analyticAt_snd
  have hP : AnalyticAt ℂ (fun w : ℂ × ℂ =>
      selfOperator w.2 (eSeries w.1 (rootGraph b0 root0 w.1) w.2)) (b0, z0) :=
    ((ContinuousLinearMap.apply ℂ V).analyticAt_bilinear
    (eSeries b0 (rootGraph b0 root0 b0) z0, selfOperator z0)).comp₂
      (f := fun w : ℂ × ℂ => eSeries w.1 (rootGraph b0 root0 w.1) w.2)
      (g := fun w : ℂ × ℂ => selfOperator w.2) (x := (b0, z0)) hE hself'
  have hQ : AnalyticAt ℂ (fun w : ℂ × ℂ =>
      mixedOperator w.2 (eSeries w.1 (rootGraph b0 root0 w.1) w.2)) (b0, z0) :=
    ((ContinuousLinearMap.apply ℂ V).analyticAt_bilinear
    (eSeries b0 (rootGraph b0 root0 b0) z0, mixedOperator z0)).comp₂
      (f := fun w : ℂ × ℂ => eSeries w.1 (rootGraph b0 root0 w.1) w.2)
      (g := fun w : ℂ × ℂ => mixedOperator w.2) (x := (b0, z0)) hE hmixed'
  have hroots : ∀ᶠ w : ℂ × ℂ in 𝓝 (b0, z0),
      (1 + w.1) * rootGraph b0 root0 w.1 ^ 2 = 1 := by
    have hf : Tendsto (Prod.fst : ℂ × ℂ → ℂ) (𝓝 (b0, z0)) (𝓝 b0) :=
      continuous_fst.continuousAt
    exact hf.eventually hspec.2.2
  have hPQ : ∀ᶠ w : ℂ × ℂ in 𝓝 (b0, z0),
      pSeries w.1 (rootGraph b0 root0 w.1) w.2 =
        selfOperator w.2 (eSeries w.1 (rootGraph b0 root0 w.1) w.2) ∧
      qSeries w.1 (rootGraph b0 root0 w.1) w.2 =
        mixedOperator w.2 (eSeries w.1 (rootGraph b0 root0 w.1) w.2) := by
    filter_upwards [original_domain_eventually hb hz, hroots] with w hw hwr
    exact original_extensions_correspondence hw.1 (rootGraph b0 root0 w.1) hwr hw.2
  refine ⟨hE, hP.congr ?_, hQ.congr ?_⟩
  · filter_upwards [hPQ] with w hw
    exact hw.1.symm
  · filter_upwards [hPQ] with w hw
    exact hw.2.symm

/-- Arbitrary external complex amplitude, including zero, on all three
unchanged original vector families along either constructed local graph. -/
theorem original_joint_hilbert_analytic_amplitude {b0 root0 z0 : ℂ}
    (hb : b0 ≠ 0) (hroot : (1 + b0) * root0 ^ 2 = 1)
    (hz : ‖z0‖ < beta b0) (amplitude : ℂ) :
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => amplitude • eSeries w.1 (rootGraph b0 root0 w.1) w.2)
        (b0, z0) ∧
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => amplitude • pSeries w.1 (rootGraph b0 root0 w.1) w.2)
        (b0, z0) ∧
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => amplitude • qSeries w.1 (rootGraph b0 root0 w.1) w.2)
        (b0, z0) := by
  obtain ⟨hE, hP, hQ⟩ := original_joint_hilbert_analytic hb hroot hz
  exact ⟨(analyticAt_const (v := amplitude)).smul hE,
    (analyticAt_const (v := amplitude)).smul hP,
    (analyticAt_const (v := amplitude)).smul hQ⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicJointHolomorphy
