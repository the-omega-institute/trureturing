/- GID: D5/S3/HilbertOperators/WuTransferReflectionBound
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/WuTransferReflectionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the linear coefficient of a matrix polynomial with scalar reflection factors. -/

import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Matrix.Order

/-!
The operator inequality used for the signed-transfer method in the rank-one
variation of Wu, arXiv:2610.33686v1, (3.54). Dividing by the scalar factors in
the left half-plane gives a contractive function on the closed right half-plane.
A temporary scalar damping factor controls the circular part of a half-disk.
-/

compile_only_with_mathlib

noncomputable section

open Filter Set
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator Topology

namespace D5.S3.HilbertOperators.WuTransferReflectionBound

private lemma norm_one_add_mul_bounds {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.re) :
    1 ≤ ‖1 + (a : ℂ) * z‖ ∧ a * ‖z‖ ≤ ‖1 + (a : ℂ) * z‖ := by
  have hsq : ‖1 + (a : ℂ) * z‖ ^ 2 = 1 + 2 * a * z.re + (a * ‖z‖) ^ 2 := by
    rw [mul_pow]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, zero_add]
    ring
  constructor
  · apply (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp
    rw [hsq]
    nlinarith [mul_nonneg ha hz]
  · apply (sq_le_sq₀ (mul_nonneg ha (norm_nonneg _)) (norm_nonneg _)).mp
    rw [hsq]
    nlinarith [mul_nonneg ha hz]

private lemma norm_le_one_on_right_half_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : ℂ → E}
    (hW : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ W z)
    (haxis : ∀ z : ℂ, z.re = 0 → ‖W z‖ ≤ 1)
    {C : ℝ} (N : ℕ)
    (hgrowth : ∀ z : ℂ, 0 ≤ z.re → 1 ≤ ‖z‖ → ‖W z‖ ≤ C * ‖z‖ ^ N)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖W z‖ ≤ 1 := by
  have hdamped (ε : ℝ) (hε : 0 < ε) :
      ‖W z‖ ≤ ‖1 + (ε : ℂ) * z‖ ^ (N + 1) := by
    obtain ⟨R, hR⟩ := exists_gt (max ‖z‖ (max 1 (C / ε ^ (N + 1))))
    have hRz := (le_max_left ‖z‖ _).trans_lt hR
    have hR1 := (le_max_left (1 : ℝ) _).trans_lt ((le_max_right ‖z‖ _).trans_lt hR)
    have hRC := (le_max_right (1 : ℝ) _).trans_lt ((le_max_right ‖z‖ _).trans_lt hR)
    let H : Set ℂ := {w | 0 ≤ w.re}
    let U : Set ℂ := Metric.ball 0 R ∩ H
    let G : ℂ → E := fun w ↦ ((1 + (ε : ℂ) * w) ^ (N + 1))⁻¹ • W w
    have hH : IsClosed H := isClosed_le continuous_const Complex.continuous_re
    have hcl : closure U ⊆ H := closure_minimal inter_subset_right hH
    have hdiff : DiffContOnCl ℂ G U := by
      apply DifferentiableOn.diffContOnCl
      intro w hw
      have hwH : 0 ≤ w.re := hcl hw
      have hden : 1 + (ε : ℂ) * w ≠ 0 := by
        intro he
        have hle : (1 : ℝ) ≤ 0 := by simpa [he] using (norm_one_add_mul_bounds hε.le hwH).1
        exact (not_le_of_gt zero_lt_one) hle
      have hp : DifferentiableAt ℂ (fun w : ℂ ↦ (1 + (ε : ℂ) * w) ^ (N + 1)) w := by
        fun_prop
      exact ((hp.inv (pow_ne_zero _ hden)).smul (hW w hwH)).differentiableWithinAt
    have hball : Bornology.IsBounded U := Metric.isBounded_ball.subset inter_subset_left
    have hboundary : ∀ w ∈ frontier U, ‖G w‖ ≤ 1 := by
      intro w hw
      have hwH : 0 ≤ w.re := hcl (frontier_subset_closure hw)
      have hlower := norm_one_add_mul_bounds hε.le hwH
      have hpos : 0 < ‖1 + (ε : ℂ) * w‖ ^ (N + 1) := pow_pos (zero_lt_one.trans_le hlower.1) _
      simp only [G, norm_smul, norm_inv, norm_pow, ← div_eq_inv_mul]
      apply (div_le_iff₀ hpos).2
      rw [one_mul]
      by_cases haxisw : w.re = 0
      · exact (haxis w haxisw).trans (one_le_pow₀ hlower.1)
      have hwR : ‖w‖ = R := by
        rcases frontier_inter_subset (Metric.ball 0 R) H hw with hw' | hw'
        · simpa [Metric.mem_sphere, dist_zero_right] using
            Metric.frontier_ball_subset_sphere hw'.1
        · exfalso
          have hOpen : IsOpen {w : ℂ | 0 < w.re} :=
            isOpen_lt continuous_const Complex.continuous_re
          have hSub : {w : ℂ | 0 < w.re} ⊆ H := by
            intro v hv
            change 0 ≤ v.re
            exact le_of_lt hv
          have hwI := interior_maximal hSub hOpen
            (show w ∈ {v : ℂ | 0 < v.re} from lt_of_le_of_ne hwH (fun h ↦ haxisw h.symm))
          exact hw'.2.2 hwI
      have hRpos : 0 < R := zero_lt_one.trans hR1
      have hc : C ≤ ε ^ (N + 1) * R :=
        (div_lt_iff₀ (pow_pos hε _)).mp hRC |>.le.trans_eq (mul_comm _ _)
      calc
        ‖W w‖ ≤ C * ‖w‖ ^ N := hgrowth w hwH (by rw [hwR]; exact hR1.le)
        _ ≤ (ε * ‖w‖) ^ (N + 1) := by
          rw [hwR, mul_pow, pow_succ R]
          calc
            C * R ^ N ≤ (ε ^ (N + 1) * R) * R ^ N :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg hRpos.le _)
            _ = ε ^ (N + 1) * (R ^ N * R) := by ring
        _ ≤ ‖1 + (ε : ℂ) * w‖ ^ (N + 1) :=
          pow_le_pow_left₀ (mul_nonneg hε.le (norm_nonneg _)) hlower.2 _
    have hzU : z ∈ U := ⟨by simpa [Metric.mem_ball, dist_zero_right] using hRz, hz⟩
    have hzG := Complex.norm_le_of_forall_mem_frontier_norm_le hball hdiff hboundary
      (subset_closure hzU)
    simp only [G, norm_smul, norm_inv, norm_pow, ← div_eq_inv_mul] at hzG
    have hpos := zero_lt_one.trans_le (norm_one_add_mul_bounds hε.le hz).1
    simpa using (div_le_iff₀ (pow_pos hpos (N + 1))).1 hzG
  have hcontinuous : Continuous (fun ε : ℝ ↦ ‖1 + (ε : ℂ) * z‖ ^ (N + 1)) := by fun_prop
  have hcontinuous0 : ContinuousWithinAt (fun ε : ℝ ↦ ‖1 + (ε : ℂ) * z‖ ^ (N + 1))
      (Ioi 0) 0 := hcontinuous.continuousAt.continuousWithinAt
  have hlim : Tendsto (fun ε : ℝ ↦ ‖1 + (ε : ℂ) * z‖ ^ (N + 1)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [ContinuousWithinAt, Complex.ofReal_zero, zero_mul, add_zero, norm_one, one_pow]
      using hcontinuous0
  exact ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun ε hε ↦ hdamped ε hε)

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- Evaluation of a matrix polynomial with coefficients indexed from zero. -/
def transferEval (A : ℕ → Matrix n n ℂ) (N : ℕ) (z : ℂ) : Matrix n n ℂ :=
  ∑ k ∈ Finset.range (N + 1), z ^ k • A k

private def scalarFactor (s : Finset ι) (a : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, (1 + (a i : ℂ) * z)

private lemma norm_scalarFactor_ge_one {s : Finset ι} {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {z : ℂ} (hz : 0 ≤ z.re) :
    1 ≤ ‖scalarFactor s a z‖ := by
  rw [scalarFactor, norm_prod]
  exact Finset.one_le_prod₀ fun i hi ↦ (norm_one_add_mul_bounds (ha i hi) hz).1

private lemma norm_transfer_le_scalarFactor {A : ℕ → Matrix n n ℂ} {N : ℕ}
    {s : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (hA : ∀ k ∈ Finset.range (N + 1), (A k).IsHermitian)
    (hreflect : ∀ z : ℂ, transferEval A N z * transferEval A N (-z) =
      (∏ i ∈ s, (1 - (a i : ℂ) ^ 2 * z ^ 2)) • (1 : Matrix n n ℂ))
    {z : ℂ} (hz : 0 ≤ z.re) : ‖transferEval A N z‖ ≤ ‖scalarFactor s a z‖ := by
  let F := transferEval A N
  let p := scalarFactor s a
  let W : ℂ → Matrix n n ℂ := fun w ↦ (p w)⁻¹ • F w
  have hp (w : ℂ) (hw : 0 ≤ w.re) : 0 < ‖p w‖ :=
    zero_lt_one.trans_le (norm_scalarFactor_ge_one ha hw)
  have hwNorm (w : ℂ) : ‖W w‖ = ‖F w‖ / ‖p w‖ := by
    simp [W, norm_smul, div_eq_inv_mul]
  have hW (w : ℂ) (hw : 0 ≤ w.re) : DifferentiableAt ℂ W w := by
    have hF : DifferentiableAt ℂ F w := by unfold F transferEval; fun_prop
    have hpoly : DifferentiableAt ℂ p w := by unfold p scalarFactor; fun_prop
    exact (hpoly.inv (norm_pos_iff.mp (hp w hw))).smul hF
  have hstar (w : ℂ) : star (F w) = F (star w) := by
    unfold F transferEval
    rw [star_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [star_smul, star_pow, show star (A k) = A k from (hA k hk).eq]
  have haxis (w : ℂ) (hw : w.re = 0) : ‖W w‖ ≤ 1 := by
    have hconj : star w = -w := by
      apply Complex.ext <;> simp [hw]
    have hprod : p w * star (p w) = ∏ i ∈ s, (1 - (a i : ℂ) ^ 2 * w ^ 2) := by
      unfold p scalarFactor
      have hreal (i : ι) : star (a i : ℂ) = (a i : ℂ) := Complex.conj_ofReal _
      simp only [star_prod, star_add, star_one, star_mul, hconj, hreal]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by ring
    have hunit : F w * star (F w) = (p w * star (p w)) • (1 : Matrix n n ℂ) := by
      rw [hstar, hconj, hprod]
      exact hreflect w
    have hsq : ‖F w‖ * ‖F w‖ ≤ ‖p w‖ * ‖p w‖ := by
      have hone : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
        rcases subsingleton_or_nontrivial (Matrix n n ℂ) with h | h
        · let := h
          rw [Subsingleton.elim (1 : Matrix n n ℂ) 0, norm_zero]
          exact zero_le_one
        · let := h
          exact CStarRing.norm_one.le
      calc
        _ = ‖F w * star (F w)‖ := CStarRing.norm_self_mul_star.symm
        _ = (‖p w‖ * ‖p w‖) * ‖(1 : Matrix n n ℂ)‖ := by
          rw [hunit, norm_smul, norm_mul, norm_star]
        _ ≤ _ := mul_le_of_le_one_right (by positivity) hone
    rw [hwNorm w, div_le_iff₀ (hp w hw.ge), one_mul]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa [pow_two] using hsq)
  let C := ∑ k ∈ Finset.range (N + 1), ‖A k‖
  have hgrowth (w : ℂ) (hw : 0 ≤ w.re) (hwlarge : 1 ≤ ‖w‖) : ‖W w‖ ≤ C * ‖w‖ ^ N := by
    rw [hwNorm w]
    refine (div_le_self (norm_nonneg _) (norm_scalarFactor_ge_one ha hw)).trans ?_
    unfold F transferEval C
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖w ^ k • A k‖ := norm_sum_le _ _
      _ ≤ _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [norm_smul, norm_pow, mul_comm (‖w‖ ^ k)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hwlarge (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (norm_nonneg _)
  have hbound := norm_le_one_on_right_half_plane hW haxis N hgrowth hz
  simpa [hwNorm z, div_le_iff₀ (hp z hz)] using hbound

private lemma hasDerivAt_transfer_zero (A : ℕ → Matrix n n ℂ) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt (fun x : ℝ ↦ transferEval A N (x : ℂ)) (A 1) 0 := by
  have hterm (k : ℕ) : HasDerivAt (fun x : ℝ ↦ x ^ k • A k)
      (if k = 1 then A k else 0) 0 := by
    have hvalue : ((k : ℝ) * (0 : ℝ) ^ (k - 1)) • A k = if k = 1 then A k else 0 := by
      obtain _ | _ | k := k <;> simp
    rw [← hvalue]
    exact (hasDerivAt_pow k (0 : ℝ)).smul_const (A k)
  have hcast (x : ℝ) (k : ℕ) : (x : ℂ) ^ k • A k = x ^ k • A k := by
    rw [← Complex.ofReal_pow]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (x ^ k) (A k)).symm
  have hsum : HasDerivAt (fun x : ℝ ↦ ∑ k ∈ Finset.range (N + 1), x ^ k • A k)
      (∑ k ∈ Finset.range (N + 1), if k = 1 then A k else 0) 0 :=
    HasDerivAt.fun_sum fun k _ ↦ hterm k
  simpa only [transferEval, hcast, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff, hN,
    ite_true] using hsum

/-- A normalized Hermitian matrix polynomial whose reflection product has the given
scalar factors has first coefficient at most the sum of their nonnegative parameters
times the identity, in the Loewner order. The parameters may vanish or repeat. -/
theorem firstCoeff_le_of_reflection {A : ℕ → Matrix n n ℂ} {N : ℕ} (hN : 1 ≤ N)
    {s : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hzero : A 0 = 1)
    (hA : ∀ k ∈ Finset.range (N + 1), (A k).IsHermitian)
    (hreflect : ∀ z : ℂ, transferEval A N z * transferEval A N (-z) =
      (∏ i ∈ s, (1 - (a i : ℂ) ^ 2 * z ^ 2)) • (1 : Matrix n n ℂ)) :
    A 1 ≤ (∑ i ∈ s, a i) • (1 : Matrix n n ℂ) := by
  classical
  let q : ℝ → ℝ := fun x ↦ ∏ i ∈ s, (1 + a i * x)
  have hq (x : ℝ) : scalarFactor s a (x : ℂ) = (q x : ℂ) := by
    simp [q, scalarFactor]
  have hqpos (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q x :=
    Finset.prod_nonneg fun i hi ↦ add_nonneg zero_le_one (mul_nonneg (ha i hi) hx)
  have hreal (x : ℝ) (hx : 0 ≤ x) : transferEval A N (x : ℂ) ≤ q x • (1 : Matrix n n ℂ) := by
    let B := transferEval A N (x : ℂ)
    have hB : IsSelfAdjoint B := by
      unfold B transferEval
      refine isSelfAdjoint_sum _ fun k hk ↦ ?_
      change star ((x : ℂ) ^ k • A k) = (x : ℂ) ^ k • A k
      rw [← Complex.ofReal_pow]
      rw [star_smul, show star ((x ^ k : ℝ) : ℂ) = ((x ^ k : ℝ) : ℂ) from Complex.conj_ofReal _,
        show star (A k) = A k from (hA k hk).eq]
    have hnorm : ‖B‖ ≤ q x := by
      simpa [B, hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqpos x hx)] using
        (norm_transfer_le_scalarFactor ha hA hreflect (z := (x : ℂ)) (by simpa))
    calc
      B ≤ algebraMap ℝ (Matrix n n ℂ) ‖B‖ := IsSelfAdjoint.le_algebraMap_norm_self B hB
      _ ≤ q x • (1 : Matrix n n ℂ) := by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.le_iff, ← sub_smul]
        exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hnorm)
  have hq' : HasDerivAt q (∑ i ∈ s, a i) 0 := by
    have hterm (i : ι) : HasDerivAt (fun x : ℝ ↦ 1 + a i * x) (a i) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (a i)).const_add 1)
    simpa [q] using HasDerivAt.fun_finsetProd (u := s) (fun i _ ↦ hterm i)
  let D : ℝ → Matrix n n ℂ := fun x ↦ q x • (1 : Matrix n n ℂ) - transferEval A N (x : ℂ)
  have hD0 : D 0 = 0 := by
    have hval : transferEval A N 0 = A 0 := by
      rw [transferEval]
      trans ∑ k ∈ Finset.range (N + 1), if k = 0 then A k else 0
      · refine Finset.sum_congr rfl fun k _ ↦ ?_
        by_cases hk : k = 0
        · simp [hk]
        · simp [hk]
      · simp [Finset.sum_ite_eq']
    simp [D, q, hval, hzero]
  have hD' : HasDerivAt D ((∑ i ∈ s, a i) • (1 : Matrix n n ℂ) - A 1) 0 :=
    (hq'.smul_const _).sub (hasDerivAt_transfer_zero A hN)
  have hlim := hD'.tendsto_slope_zero_right
  have hnonneg : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 ≤ x⁻¹ • (D (0 + x) - D 0) := by
    refine eventually_mem_nhdsWithin.mono fun x hx ↦ ?_
    have hx' : 0 < x := hx
    rw [zero_add, hD0, sub_zero]
    exact ((Matrix.le_iff.mp (hreal x hx'.le)).smul (inv_nonneg.mpr hx'.le)).nonneg
  have hderiv_nonneg : 0 ≤ (∑ i ∈ s, a i) • (1 : Matrix n n ℂ) - A 1 :=
    ge_of_tendsto hlim hnonneg
  exact Matrix.le_iff.mpr (Matrix.nonneg_iff_posSemidef.mp hderiv_nonneg)

end D5.S3.HilbertOperators.WuTransferReflectionBound
