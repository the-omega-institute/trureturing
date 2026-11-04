/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bilinear trace-log derivative exchange on the original infinite carrier. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-! Analytic identities for the original signed Gaussian operator and its literal cutoffs. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear

open OriginalGaussianMatrix OriginalGaussianResolvent
open OriginalGaussianWeightedResolvent OriginalGaussianDeterminant
open OriginalGaussianFiniteTrace OriginalGaussianUniformCutoff

private def traceBilinear (u v : H) : ℂ := ∑' n : ℕ, u n * v n

private lemma traceBilinear_norm_summable (u v : H) :
    Summable (fun n : ℕ => ‖u n * v n‖) := by
  simpa only [norm_mul] using lp.summable_mul (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two) u v

private lemma traceBilinear_bound (u v : H) :
    ‖traceBilinear u v‖ ≤ ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ∑' n : ℕ, ‖u n * v n‖ :=
      norm_tsum_le_tsum_norm (traceBilinear_norm_summable u v)
    _ = ∑' n : ℕ, ‖u n‖ * ‖v n‖ := by simp only [norm_mul]
    _ ≤ _ := lp.tsum_mul_le_mul_norm'
      (by simpa using Real.HolderConjugate.two_two) u v

private lemma traceBilinear_comm (u v : H) :
    traceBilinear u v = traceBilinear v u := by
  unfold traceBilinear
  exact tsum_congr (fun _ => mul_comm _ _)

private lemma traceBilinear_add_right (u v w : H) :
    traceBilinear u (v + w) = traceBilinear u v + traceBilinear u w := by
  change (∑' n : ℕ, u n * (v n + w n)) = _
  simp_rw [mul_add]
  exact (traceBilinear_norm_summable u v).of_norm.tsum_add
    (traceBilinear_norm_summable u w).of_norm

private lemma traceBilinear_smul_right (u v : H) (c : ℂ) :
    traceBilinear u (c • v) = c * traceBilinear u v := by
  change (∑' n : ℕ, u n * (c * v n)) = c * ∑' n : ℕ, u n * v n
  rw [← tsum_mul_left]
  exact tsum_congr (fun _ => by ring)

private def traceBilinearCLM (u : H) : H →L[ℂ] ℂ :=
  ({ toFun := traceBilinear u
     map_add' := traceBilinear_add_right u
     map_smul' := fun c v => traceBilinear_smul_right u v c } : H →ₗ[ℂ] ℂ).mkContinuous
    ‖u‖ (traceBilinear_bound u)

private lemma traceBilinear_sub_left (u v w : H) :
    traceBilinear (u - v) w = traceBilinear u w - traceBilinear v w := by
  rw [traceBilinear_comm (u - v) w]
  change traceBilinearCLM w (u - v) = _
  rw [map_sub]
  exact congrArg₂ (fun a b : ℂ => a - b)
    (traceBilinear_comm w u) (traceBilinear_comm w v)

private def traceMomentCLM (u : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  ({ toFun := fun T => traceBilinear u (T u)
     map_add' := fun T S => by
       change traceBilinear u (T u + S u) = _
       exact traceBilinear_add_right u (T u) (S u)
     map_smul' := fun c T => by
       change traceBilinear u (c • T u) = _
       exact traceBilinear_smul_right u (T u) c } : (H →L[ℂ] H) →ₗ[ℂ] ℂ).mkContinuous
    (‖u‖ * ‖u‖) (fun T => by
      calc
        _ ≤ ‖u‖ * ‖T u‖ := traceBilinear_bound u (T u)
        _ ≤ ‖u‖ * (‖T‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm u) (norm_nonneg _)
        _ = (‖u‖ * ‖u‖) * ‖T‖ := by ring)

/- The support reduction uses only the first vector's support. In particular
   p=0 and N=0 require no false assertion that the identity has finite range. -/
private lemma traceCutoff_coordinate (N : ℕ) (r : ℝ) (n : ℕ) :
    weightedCutoff N r n = if n < N then (n + 1 : ℂ) * sourceValue r n else 0 := by
  classical
  simp only [weightedCutoff, traceWeightedTerm, lp.coeFn_sum, lp.coeFn_single]
  by_cases hn : n < N <;> simp [Finset.mem_range, hn]

private lemma traceCutoff_basis_expansion (N : ℕ) (r : ℝ) :
    weightedCutoff N r = ∑ j : Fin N,
      ((j.val + 1 : ℂ) * sourceValue r j.val) • basis j.val := by
  classical
  unfold weightedCutoff
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  change (lp.single 2 j.val ((j.val + 1 : ℂ) * sourceValue r j.val) : H) =
    ((j.val + 1 : ℂ) * sourceValue r j.val) • (lp.single 2 j.val (1 : ℂ) : H)
  simpa only [smul_eq_mul, mul_one] using
    lp.single_smul (E := fun _ : ℕ => ℂ) 2 j.val
      ((j.val + 1 : ℂ) * sourceValue r j.val) (1 : ℂ)

private lemma traceCutoff_power_coordinate (N p : ℕ) (r : ℝ) (i : Fin N) :
    ((sectionOp N (Real.sqrt r : ℂ) ^ p) (weightedCutoff N r)) i.val =
      ∑ j : Fin N, (finiteSection N (Real.sqrt r : ℂ) ^ p) i j *
        ((j.val + 1 : ℂ) * sourceValue r j.val) := by
  rw [traceCutoff_basis_expansion, map_sum]
  simp only [map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [unit1Section_power_coordinate]
  exact mul_comm _ _

/-- The literal finite matrix moment equals its actual l2 cutoff contraction.
    No radial-domain hypothesis is needed for this finite algebraic identity. -/
theorem finiteTraceMoment_eq_actual_cutoff_bilinear (N p : ℕ) (r : ℝ) :
    finiteTraceMoment N p r = ∑' n : ℕ, weightedCutoff N r n *
      ((sectionOp N (Real.sqrt r : ℂ) ^ p) (weightedCutoff N r)) n := by
  classical
  symm
  rw [tsum_eq_sum (s := Finset.range N)
    (f := fun n : ℕ => weightedCutoff N r n *
      ((sectionOp N (Real.sqrt r : ℂ) ^ p) (weightedCutoff N r)) n) (fun n hn => by
    rw [traceCutoff_coordinate, if_neg (by simpa only [Finset.mem_range] using hn),
      zero_mul])]
  rw [Finset.sum_range]
  unfold finiteTraceMoment
  apply Finset.sum_congr rfl
  intro i _
  rw [traceCutoff_coordinate, if_pos i.isLt, traceCutoff_power_coordinate,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [traceFiniteWeight]
  ring

private lemma traceOddPowers_norm_summable {T : H →L[ℂ] H} (hT : ‖T‖ < 1) :
    Summable (fun k : ℕ => ‖T ^ (2 * k + 1)‖) := by
  have hq : ‖T‖ ^ 2 < 1 :=
    pow_lt_one₀ (norm_nonneg T) hT (by norm_num : (2 : ℕ) ≠ 0)
  have hg : Summable (fun k : ℕ => ‖T‖ ^ (2 * k + 1)) := by
    convert (summable_geometric_of_lt_one (sq_nonneg ‖T‖) hq).mul_left ‖T‖ using 1
    ext k
    rw [pow_add, pow_one, pow_mul]
    ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_pow_le T (2 * k + 1)) hg

private lemma traceOddPowers_eq_signed_difference {T : H →L[ℂ] H} (hT : ‖T‖ < 1) :
    (∑' k : ℕ, T ^ (2 * k + 1)) = (1 / 2 : ℂ) •
      ((∑' k : ℕ, T ^ k) - (∑' k : ℕ, (-T) ^ k)) := by
  let Rm : H →L[ℂ] H := ∑' k : ℕ, T ^ k
  let Rp : H →L[ℂ] H := ∑' k : ℕ, (-T) ^ k
  let S : H →L[ℂ] H := ∑' k : ℕ, (T ^ 2) ^ k
  have hT2 : ‖T ^ 2‖ < 1 := (norm_pow_le T 2).trans_lt
    (pow_lt_one₀ (norm_nonneg T) hT (by norm_num : (2 : ℕ) ≠ 0))
  have hs := summable_geometric_of_norm_lt_one hT2
  have hm : Rm * (1 - T) = 1 :=
    (summable_geometric_of_norm_lt_one hT).tsum_pow_mul_one_sub
  have hn : ‖-T‖ < 1 := by simpa only [norm_neg] using hT
  have hp : Rp * (1 + T) = 1 := by
    simpa only [sub_neg_eq_add] using
      (summable_geometric_of_norm_lt_one hn).tsum_pow_mul_one_sub
  have hS : (1 - T ^ 2) * S = 1 := hs.one_sub_mul_tsum_pow
  have ho : (∑' k : ℕ, T ^ (2 * k + 1)) = T * S := by
    rw [← hs.tsum_mul_left T]
    apply tsum_congr
    intro k
    rw [← pow_mul, ← pow_succ']
  have he : Rm - Rp = T * S + T * S := by
    calc
      _ = ((Rm - Rp) * (1 - T ^ 2)) * S := by
        rw [mul_assoc, hS, mul_one]
      _ = ((Rm * (1 - T)) * (1 + T) -
          (Rp * (1 + T)) * (1 - T)) * S := by noncomm_ring
      _ = T * S + T * S := by rw [hm, hp]; noncomm_ring
  rw [ho]
  change T * S = (1 / 2 : ℂ) • (Rm - Rp)
  rw [he, smul_add]
  module

private lemma traceOddMoments {T : H →L[ℂ] H} (hT : ‖T‖ < 1) (u : H) :
    Summable (fun k : ℕ => ‖traceBilinear u ((T ^ (2 * k + 1)) u)‖) ∧
      (∑' k : ℕ, traceBilinear u ((T ^ (2 * k + 1)) u)) =
        (1 / 2 : ℂ) *
          (traceBilinear u ((∑' k : ℕ, T ^ k) u) -
            traceBilinear u ((∑' k : ℕ, (-T) ^ k) u)) := by
  have hs := traceOddPowers_norm_summable hT
  constructor
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by
        change ‖traceMomentCLM u (T ^ (2 * k + 1))‖ ≤ _
        exact (traceMomentCLM u).le_opNorm _) (hs.mul_left ‖traceMomentCLM u‖)
  · change (∑' k : ℕ, traceMomentCLM u (T ^ (2 * k + 1))) = _
    rw [← (traceMomentCLM u).map_tsum hs.of_norm,
      traceOddPowers_eq_signed_difference hT, map_smul, map_sub]
    rfl

private lemma traceRadial_section_norm_lt_one (N : ℕ) {r : ℝ}
    (hr1 : r < 1) : ‖sectionOp N (Real.sqrt r : ℂ)‖ < 1 := by
  have hz := radial_norm_lt_one hr1
  exact (sectionOp_norm_le N hz).trans_lt
    (pow_lt_one₀ (norm_nonneg _) hz (by norm_num : (2 : ℕ) ≠ 0))

private lemma finite_odd_moment_series_eq_signed_inverse_difference (N : ℕ)
    {r : ℝ} (hr1 : r < 1) :
    Summable (fun k : ℕ => ‖finiteTraceMoment N (2 * k + 1) r‖) ∧
      (∑' k : ℕ, finiteTraceMoment N (2 * k + 1) r) = (1 / 2 : ℂ) *
        (traceBilinear (weightedCutoff N r)
          (sectionSignedResolvent N 1 (Real.sqrt r : ℂ) (weightedCutoff N r)) -
         traceBilinear (weightedCutoff N r)
          (sectionSignedResolvent N (-1) (Real.sqrt r : ℂ) (weightedCutoff N r))) := by
  simp_rw [finiteTraceMoment_eq_actual_cutoff_bilinear]
  simpa only [sectionSignedResolvent, one_smul, neg_one_smul, traceBilinear] using
    traceOddMoments (traceRadial_section_norm_lt_one N hr1) (weightedCutoff N r)

/-- Odd moments of the actual original operator and actual weightedSource.
    The three summability clauses include absolute convergence of the odd
    scalar series and of both signed inverse contractions. -/
theorem actual_odd_moment_series_eq_signed_inverse_difference {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun k : ℕ => ‖∑' n : ℕ, weightedSource r hr.le hr1 n *
      ((operator (Real.sqrt r : ℂ) ^ (2 * k + 1)) (weightedSource r hr.le hr1)) n‖) ∧
    Summable (fun n : ℕ => ‖weightedSource r hr.le hr1 n *
      OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n‖) ∧
    Summable (fun n : ℕ => ‖weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n‖) ∧
    (∑' k : ℕ, ∑' n : ℕ, weightedSource r hr.le hr1 n *
      ((operator (Real.sqrt r : ℂ) ^ (2 * k + 1)) (weightedSource r hr.le hr1)) n) =
      (1 / 2 : ℂ) *
        ((∑' n : ℕ, weightedSource r hr.le hr1 n *
          OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n) -
         (∑' n : ℕ, weightedSource r hr.le hr1 n *
          oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n)) := by
  have hz := radial_norm_lt_one hr1
  have hT : ‖operator (Real.sqrt r : ℂ)‖ < 1 :=
    (operator_norm_le hz).trans_lt
      (pow_lt_one₀ (norm_nonneg _) hz (by norm_num : (2 : ℕ) ≠ 0))
  have h := traceOddMoments hT (weightedSource r hr.le hr1)
  exact ⟨h.1, traceBilinear_norm_summable _ _, traceBilinear_norm_summable _ _,
    by simpa only [traceBilinear, OriginalGaussianResolvent.resolvent, oppositeResolvent] using h.2⟩

/- A total parameter function makes the open-set derivative-limit API usable.
   On the radial domain it is proved equal to the existing weightedSource. -/
private def traceWeightVector (t : ℝ) : H :=
  ∑' n : ℕ, lp.single 2 n ((n + 1 : ℂ) * sourceValue t n)

private lemma traceWeightVector_eq {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    traceWeightVector t = weightedSource t ht ht1 := by
  simpa only [traceWeightVector, traceWeightedTerm] using
    traceWeightedTerm_tsum ht ht1

private lemma traceWeightVector_uniform {a R : ℝ} (ha : 0 < a)
    (haR : a < R) (hR1 : R < 1) :
    TendstoUniformlyOn weightedCutoff traceWeightVector atTop (Set.Ioo a R) := by
  have hR : 0 ≤ R := (ha.trans haR).le
  have h := weightedCutoff_tendstoUniformly hR hR1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := Metric.tendstoUniformly_iff.mp h ε hε
  filter_upwards [he] with N hN t ht
  have ht0 : 0 ≤ t := (ha.trans ht.1).le
  simpa only [traceWeightVector_eq ht0 (ht.2.trans hR1)] using
    hN (⟨t, ht0, ht.2.le⟩ : Set.Icc (0 : ℝ) R)

private lemma traceWeightVector_norm_le {R t : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (ht : 0 ≤ t) (htR : t ≤ R) : ‖traceWeightVector t‖ ≤ traceWeightMass R := by
  have h := (weightedCutoff_tendstoUniformly hR hR1).tendsto_at
    (⟨t, ht, htR⟩ : Set.Icc (0 : ℝ) R)
  rw [← traceWeightVector_eq ht (htR.trans_lt hR1)] at h
  exact le_of_tendsto h.norm (Eventually.of_forall
    (fun N => weightedCutoff_norm_le N htR hR hR1))

private def traceRadialSignedInverse (σ : ℂ) (t : ℝ) : H →L[ℂ] H :=
  ∑' k : ℕ, (σ • operator (Real.sqrt t : ℂ)) ^ k

private lemma traceRadial_sqrt_norm (t : ℝ) :
    ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private lemma traceRadial_signed_uniform {a R : ℝ} (ha : 0 < a)
    (haR : a < R) (hR1 : R < 1) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    TendstoUniformlyOn (fun N t => sectionSignedResolvent N σ (Real.sqrt t : ℂ))
      (traceRadialSignedInverse σ) atTop (Set.Ioo a R) := by
  have hR : 0 ≤ R := (ha.trans haR).le
  have hρ1 : Real.sqrt R < 1 :=
    (Real.sqrt_lt hR zero_le_one).mpr (by simpa using hR1)
  have h := sectionSignedResolvent_tendstoUniformlyOn (Real.sqrt_nonneg R) hρ1 σ hσ
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  apply hN
  change ‖(Real.sqrt t : ℂ)‖ ≤ Real.sqrt R
  rw [traceRadial_sqrt_norm]
  exact Real.sqrt_le_sqrt ht.2.le

private lemma traceRadial_signed_norm_le {R t : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (ht : 0 ≤ t) (htR : t ≤ R) (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) :
    ‖sectionSignedResolvent N σ (Real.sqrt t : ℂ)‖ ≤ (1 - R)⁻¹ ∧
      ‖traceRadialSignedInverse σ t‖ ≤ (1 - R)⁻¹ := by
  have hz := radial_norm_lt_one (htR.trans_lt hR1)
  have he : ‖(Real.sqrt t : ℂ)‖ ^ 2 = t := by
    rw [traceRadial_sqrt_norm, Real.sq_sqrt ht]
  have hn : ‖σ • sectionOp N (Real.sqrt t : ℂ)‖ ≤ R := by
    rw [norm_smul, hσ, one_mul]
    exact (sectionOp_norm_le N hz).trans (by simpa only [he] using htR)
  have hi : ‖σ • operator (Real.sqrt t : ℂ)‖ ≤ R := by
    rw [norm_smul, hσ, one_mul]
    exact (operator_norm_le hz).trans (by simpa only [he] using htR)
  exact ⟨traceNeumann_norm_le hR hR1 hn, traceNeumann_norm_le hR hR1 hi⟩

/- Telescoping in the vector twice and in the operator once proves the
   quadratic pairing error. No Hermitian inner-product API is used. -/
private lemma traceBilinear_moment_error (T S : H →L[ℂ] H) (u w : H) :
    ‖traceBilinear u (T u) - traceBilinear w (S w)‖ ≤
      (‖T‖ * (‖u‖ + ‖w‖)) * ‖u - w‖ + ‖w‖ ^ 2 * ‖T - S‖ := by
  have h₁ : ‖traceBilinear u (T u) - traceBilinear w (T u)‖ ≤
      ‖u - w‖ * (‖T‖ * ‖u‖) := by
    rw [← traceBilinear_sub_left]
    exact (traceBilinear_bound _ _).trans
      (mul_le_mul_of_nonneg_left (T.le_opNorm u) (norm_nonneg _))
  have h₂ : ‖traceBilinear w (T u) - traceBilinear w (T w)‖ ≤
      ‖w‖ * (‖T‖ * ‖u - w‖) := by
    change ‖traceBilinearCLM w (T u) - traceBilinearCLM w (T w)‖ ≤ _
    rw [← map_sub, ← T.map_sub]
    exact (traceBilinear_bound _ _).trans
      (mul_le_mul_of_nonneg_left (T.le_opNorm (u - w)) (norm_nonneg _))
  have h₃ : ‖traceBilinear w (T w) - traceBilinear w (S w)‖ ≤
      ‖w‖ * (‖T - S‖ * ‖w‖) := by
    change ‖traceBilinearCLM w (T w) - traceBilinearCLM w (S w)‖ ≤ _
    rw [← map_sub]
    change ‖traceBilinear w ((T - S) w)‖ ≤ _
    exact (traceBilinear_bound _ _).trans
      (mul_le_mul_of_nonneg_left ((T - S).le_opNorm w) (norm_nonneg _))
  calc
    _ ≤ ‖traceBilinear u (T u) - traceBilinear w (T u)‖ +
        ‖traceBilinear w (T u) - traceBilinear w (S w)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖u - w‖ * (‖T‖ * ‖u‖) +
        (‖traceBilinear w (T u) - traceBilinear w (T w)‖ +
          ‖traceBilinear w (T w) - traceBilinear w (S w)‖) :=
      add_le_add h₁ (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ ‖u - w‖ * (‖T‖ * ‖u‖) +
        (‖w‖ * (‖T‖ * ‖u - w‖) + ‖w‖ * (‖T - S‖ * ‖w‖)) :=
      add_le_add le_rfl (add_le_add h₂ h₃)
    _ = _ := by ring

private lemma traceBilinear_moment_uniform {α : Type*} {s : Set α}
    {uN : ℕ → α → H} {u : α → H}
    {TN : ℕ → α → (H →L[ℂ] H)} {T : α → (H →L[ℂ] H)} {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hu : TendstoUniformlyOn uN u atTop s)
    (hT : TendstoUniformlyOn TN T atTop s)
    (huN : ∀ N t, t ∈ s → ‖uN N t‖ ≤ M)
    (huw : ∀ t, t ∈ s → ‖u t‖ ≤ M)
    (hTN : ∀ N t, t ∈ s → ‖TN N t‖ ≤ L) :
    TendstoUniformlyOn (fun N t => traceBilinear (uN N t) (TN N t (uN N t)))
      (fun t => traceBilinear (u t) (T t (u t))) atTop s := by
  let C₁ : ℝ := L * (2 * M)
  let C₂ : ℝ := M ^ 2
  have h₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have h₂ : 0 ≤ C₂ := sq_nonneg M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := ε / (C₁ + C₂ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hU := Metric.tendstoUniformlyOn_iff.mp hu δ hδ
  have hA := Metric.tendstoUniformlyOn_iff.mp hT δ hδ
  filter_upwards [hU, hA] with N hUN hAN t ht
  have hUt : ‖uN N t - u t‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hUN t ht
  have hAt : ‖TN N t - T t‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hAN t ht
  rw [dist_comm, dist_eq_norm]
  calc
    _ ≤ (‖TN N t‖ * (‖uN N t‖ + ‖u t‖)) * ‖uN N t - u t‖ +
        ‖u t‖ ^ 2 * ‖TN N t - T t‖ := traceBilinear_moment_error _ _ _ _
    _ ≤ C₁ * ‖uN N t - u t‖ + C₂ * ‖TN N t - T t‖ := by
      have hc₁ : ‖TN N t‖ * (‖uN N t‖ + ‖u t‖) ≤ C₁ := by
        apply mul_le_mul (hTN N t ht) ?_ (by positivity) hL
        linarith [huN N t ht, huw t ht]
      have hc₂ : ‖u t‖ ^ 2 ≤ C₂ :=
        pow_le_pow_left₀ (norm_nonneg _) (huw t ht) 2
      exact add_le_add (mul_le_mul_of_nonneg_right hc₁ (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hc₂ (norm_nonneg _))
    _ ≤ C₁ * δ + C₂ * δ := add_le_add
      (mul_le_mul_of_nonneg_left hUt.le h₁) (mul_le_mul_of_nonneg_left hAt.le h₂)
    _ < (C₁ + C₂ + 1) * δ := by nlinarith
    _ = ε := by
      dsimp [δ]
      field_simp [ne_of_gt (by positivity : 0 < C₁ + C₂ + 1)]

private def traceSignedScalar (N : ℕ) (σ : ℂ) (t : ℝ) : ℂ :=
  traceBilinear (weightedCutoff N t)
    (sectionSignedResolvent N σ (Real.sqrt t : ℂ) (weightedCutoff N t))

private def traceLimitSignedScalar (σ : ℂ) (t : ℝ) : ℂ :=
  traceBilinear (traceWeightVector t) (traceRadialSignedInverse σ t (traceWeightVector t))

private lemma traceSignedScalar_uniform {a R : ℝ} (ha : 0 < a)
    (haR : a < R) (hR1 : R < 1) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    TendstoUniformlyOn (fun N => traceSignedScalar N σ)
      (traceLimitSignedScalar σ) atTop (Set.Ioo a R) := by
  have hR : 0 ≤ R := (ha.trans haR).le
  have hM : 0 ≤ traceWeightMass R :=
    tsum_nonneg (fun n => by unfold traceWeightBound; positivity)
  have hL : 0 ≤ (1 - R)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hR1.le)
  exact traceBilinear_moment_uniform hM hL
    (traceWeightVector_uniform ha haR hR1) (traceRadial_signed_uniform ha haR hR1 σ hσ)
    (fun N t ht => weightedCutoff_norm_le N ht.2.le hR hR1)
    (fun t ht => traceWeightVector_norm_le hR hR1 (ha.trans ht.1).le ht.2.le)
    (fun N t ht => (traceRadial_signed_norm_le hR hR1
      (ha.trans ht.1).le ht.2.le σ hσ N).1)

private def traceRadialDerivative (t : ℝ) : ℂ :=
  -(1 / (2 * (t : ℂ))) * (traceLimitSignedScalar 1 t - traceLimitSignedScalar (-1) t)

private lemma traceFiniteDerivative_eq (N : ℕ) {t : ℝ} (ht1 : t < 1) :
    -((1 / (t : ℂ)) * ∑' k : ℕ, finiteTraceMoment N (2 * k + 1) t) =
      -(1 / (2 * (t : ℂ))) * (traceSignedScalar N 1 t - traceSignedScalar N (-1) t) := by
  rw [(finite_odd_moment_series_eq_signed_inverse_difference N ht1).2]
  dsimp only [traceSignedScalar]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private lemma traceFiniteDerivatives_uniform {a R : ℝ} (ha : 0 < a)
    (haR : a < R) (hR1 : R < 1) :
    TendstoUniformlyOn
      (fun N (t : ℝ) => -((1 / (t : ℂ)) * ∑' k : ℕ, finiteTraceMoment N (2 * k + 1) t))
      traceRadialDerivative atTop (Set.Ioo a R) := by
  have hm := traceSignedScalar_uniform ha haR hR1 1 (by norm_num)
  have hp := traceSignedScalar_uniform ha haR hR1 (-1) (by norm_num)
  let C : ℝ := 1 / (2 * a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hM := Metric.tendstoUniformlyOn_iff.mp hm δ hδ
  have hP := Metric.tendstoUniformlyOn_iff.mp hp δ hδ
  filter_upwards [hM, hP] with N hMN hPN t ht
  have ht0 : 0 < t := ha.trans ht.1
  have hmt : ‖traceSignedScalar N 1 t - traceLimitSignedScalar 1 t‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hMN t ht
  have hpt : ‖traceSignedScalar N (-1) t - traceLimitSignedScalar (-1) t‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hPN t ht
  have hcoef : ‖-(1 / (2 * (t : ℂ)))‖ ≤ C := by
    rw [norm_neg, norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left ht.1.le (by norm_num))
  rw [dist_comm, dist_eq_norm, traceFiniteDerivative_eq N (ht.2.trans hR1)]
  change ‖-(1 / (2 * (t : ℂ))) *
      (traceSignedScalar N 1 t - traceSignedScalar N (-1) t) -
    -(1 / (2 * (t : ℂ))) *
      (traceLimitSignedScalar 1 t - traceLimitSignedScalar (-1) t)‖ < ε
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ C * (‖traceSignedScalar N 1 t - traceLimitSignedScalar 1 t‖ +
        ‖traceSignedScalar N (-1) t - traceLimitSignedScalar (-1) t‖) := by
      apply mul_le_mul hcoef ?_ (norm_nonneg _) hC
      have he : (traceSignedScalar N 1 t - traceSignedScalar N (-1) t) -
          (traceLimitSignedScalar 1 t - traceLimitSignedScalar (-1) t) =
          (traceSignedScalar N 1 t - traceLimitSignedScalar 1 t) -
            (traceSignedScalar N (-1) t - traceLimitSignedScalar (-1) t) := by ring
      rw [he]
      exact norm_sub_le _ _
    _ ≤ (C + 1) * (‖traceSignedScalar N 1 t - traceLimitSignedScalar 1 t‖ +
        ‖traceSignedScalar N (-1) t - traceLimitSignedScalar (-1) t‖) := by
      exact mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ < (C + 1) * (δ + δ) :=
      mul_lt_mul_of_pos_left (add_lt_add hmt hpt) (by positivity)
    _ = ε := by
      dsimp [δ]
      field_simp [ne_of_gt (by positivity : 0 < C + 1)]
      <;> ring

/-- All finite derivatives converge uniformly on an OPEN interval, and the
    pinned derivative-limit theorem gives the actual gaussianLogDet derivative.
    The total W in this statement equals weightedSource at every interval point. -/
theorem compact_uniform_scalar_derivatives_and_final_exchange {a R : ℝ}
    (ha : 0 < a) (haR : a < R) (hR1 : R < 1) :
    let W : ℝ → H := fun t => ∑' n : ℕ,
      lp.single 2 n ((n + 1 : ℂ) * sourceValue t n)
    let G : ℝ → ℂ := fun t => -(1 / (2 * (t : ℂ))) *
      ((∑' n : ℕ, W t n * OriginalGaussianResolvent.resolvent (Real.sqrt t : ℂ) (W t) n) -
       (∑' n : ℕ, W t n * oppositeResolvent (Real.sqrt t : ℂ) (W t) n))
    TendstoUniformlyOn
      (fun N (t : ℝ) => -((1 / (t : ℂ)) * ∑' k : ℕ, finiteTraceMoment N (2 * k + 1) t))
      G atTop (Set.Ioo a R) ∧
    ∀ t ∈ Set.Ioo a R,
      HasDerivAt (fun s : ℝ => gaussianLogDet (Real.sqrt s : ℂ)) (G t) t := by
  have hu := traceFiniteDerivatives_uniform ha haR hR1
  have hd : ∀ t ∈ Set.Ioo a R,
      HasDerivAt (fun s : ℝ => gaussianLogDet (Real.sqrt s : ℂ))
        (traceRadialDerivative t) t := by
    intro t ht
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hu
      (Eventually.of_forall (fun N s hs =>
        finiteLog_hasDerivAt_traceMoments N (ha.trans hs.1) (hs.2.trans hR1)))
      (fun s hs => finiteLog_tendsto (radial_norm_lt_one (hs.2.trans hR1))) ht
  constructor
  · convert hu using 1
    funext t
    simp only [traceRadialDerivative, traceLimitSignedScalar, traceBilinear,
      traceRadialSignedInverse, one_smul, neg_one_smul,
      OriginalGaussianResolvent.resolvent, oppositeResolvent, traceWeightVector]
  · intro t ht
    convert hd t ht using 1 <;>
      simp only [traceRadialDerivative, traceLimitSignedScalar, traceBilinear,
        traceRadialSignedInverse, one_smul, neg_one_smul,
        OriginalGaussianResolvent.resolvent, oppositeResolvent, traceWeightVector]

/-- The original radial trace-log derivative, in the literal unconjugated
    signed-inverse form on the original infinite carrier. -/
theorem gaussianLogDet_hasDerivAt_bilinear_resolvent {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t : ℝ => gaussianLogDet (Real.sqrt t : ℂ))
      (-(1 / (2 * (r : ℂ))) *
        ((∑' n : ℕ, weightedSource r hr.le hr1 n *
          OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n) -
         (∑' n : ℕ, weightedSource r hr.le hr1 n *
          oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n))) r := by
  have ha : 0 < r / 2 := by linarith
  have haR : r / 2 < (r + 1) / 2 := by linarith
  have hR1 : (r + 1) / 2 < 1 := by linarith
  have hm : r ∈ Set.Ioo (r / 2) ((r + 1) / 2) := by constructor <;> linarith
  have h := (compact_uniform_scalar_derivatives_and_final_exchange ha haR hR1).2 r hm
  have hw : (∑' n : ℕ, lp.single 2 n ((n + 1 : ℂ) * sourceValue r n)) =
      weightedSource r hr.le hr1 := traceWeightVector_eq hr.le hr1
  simpa only [hw] using h

/-- The radial logarithmic derivative of the actual Gaussian closed-cycle
    determinant, consuming the finite-trace exchange and BOTH actual weighted
    inverse scalars from the original operator and weighted-resolvent formulas. -/
theorem gaussianLogDet_hasDerivAt_period {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t : ℝ => gaussianLogDet (Real.sqrt t : ℂ))
      ((deriv F r / F r - 1 / (4 * (1 - r)) : ℝ) : ℂ) r := by
  have hd := gaussianLogDet_hasDerivAt_bilinear_resolvent hr hr1
  rw [(OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar
      hr hr1).2, (bilinear_opposite_resolvent_scalar hr hr1).2] at hd
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : 1 - (r : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith : (1 : ℝ) - r ≠ 0)
  have hF : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)))
  have he : -(1 / (2 * (r : ℂ))) *
      (((3 * r / (4 * (1 - r)) - 2 * r * deriv F r / F r : ℝ) : ℂ) -
       ((r / (4 * (1 - r)) : ℝ) : ℂ)) =
        ((deriv F r / F r - 1 / (4 * (1 - r)) : ℝ) : ℂ) := by
    push_cast
    field_simp [hr0, h1, hF]
    <;> ring
  rw [he] at hd
  exact hd

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear
