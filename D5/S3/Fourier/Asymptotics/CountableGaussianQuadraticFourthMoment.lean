/- GID: D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian quadratic series converge in L4 with exact second and fourth moments. -/

import D5.S3.Fourier.Asymptotics.GaussianEvenMoment
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
The scalar even moments used here are supplied by GaussianEvenMoment.
The countable quadratic-series proof uses their exact standard-normal specialization.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The actual countable centered Gaussian quadratic series converges in L4 and L2.
Its moments are determined by the square and fourth-power sums of its real coefficients. -/
theorem result (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hG : ∀ j, HasLaw (G j) (gaussianReal 0 1) P)
    (hind : iIndepFun G P) (ha : Summable (fun j => (a j) ^ 2)) :
    let : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
    ∃ (hm : ∀ j, MemLp (fun ω => a j * ((G j ω) ^ 2 - 1)) 4 P)
      (X : Lp ℝ 4 P),
      HasSum (fun j => (hm j).toLp (fun ω => a j * ((G j ω) ^ 2 - 1))) X ∧
      MemLp (fun ω => X ω) 2 P ∧
      Tendsto (fun s : Finset ℕ => eLpNorm
        ((fun ω => ∑ j ∈ s, a j * ((G j ω) ^ 2 - 1)) - ⇑X) 2 P) atTop (𝓝 0) ∧
      (∫ ω, X ω ∂P) = 0 ∧
      (∫ ω, (X ω) ^ 2 ∂P) = 2 * ∑' j, (a j) ^ 2 ∧
      (∫ ω, (X ω) ^ 4 ∂P) = 12 * (∑' j, (a j) ^ 2) ^ 2 + 48 * ∑' j, (a j) ^ 4 ∧
      (∫ ω, (X ω) ^ 4 ∂P) ≤ 15 * (∫ ω, (X ω) ^ 2 ∂P) ^ 2 := by
  classical
  let : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  have hgaussian := GaussianEvenMoment.centralMoment_two_mul
  have hmoment (n : ℕ) : (∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 1) =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) := by
    simpa [centralMoment, integral_id_gaussianReal] using hgaussian 0 1 n
  have hLp (j : ℕ) (p : ℝ≥0) : MemLp (G j) p P := by
    have hm : MemLp id p (P.map (G j)) := by
      rw [(hG j).map_eq]
      exact memLp_id_gaussianReal p
    simpa only [Function.id_comp] using
      (memLp_map_measure_iff aestronglyMeasurable_id (hG j).aemeasurable).mp hm
  have hsq (j : ℕ) (p : ℝ≥0) : MemLp (fun ω => (G j ω) ^ 2) p P := by
    simpa [ENNReal.coe_mul, ENNReal.mul_div_cancel_right
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞), Real.rpow_two] using
      (hLp j (p * 2)).norm_rpow_div 2
  let F : ℕ → Ω → ℝ := fun j ω => a j * ((G j ω) ^ 2 - 1)
  have hF (j : ℕ) (p : ℝ≥0) : MemLp (F j) p P :=
    ((hsq j p).sub (memLp_const (1 : ℝ))).const_mul (a j)
  have hpow {f : Ω → ℝ} (n : ℕ) (hf : MemLp f n P) :
      Integrable (fun ω => (f ω) ^ n) P := by
    apply (hf.integrable_norm_pow').mono' (hf.aestronglyMeasurable.pow n)
    filter_upwards [] with ω
    simp [norm_pow]
  have hGmom (j n : ℕ) : (∫ ω, (G j ω) ^ (2 * n) ∂P) =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) := by
    exact ((hG j).integral_comp (f := fun x : ℝ => x ^ (2 * n)) (by fun_prop)).trans
      (hmoment n)
  have hg2 (j : ℕ) : (∫ ω, (G j ω) ^ 2 ∂P) = 1 := by
    simpa using hGmom j 1
  have hg4 (j : ℕ) : (∫ ω, (G j ω) ^ 4 ∂P) = 3 := by
    simpa using hGmom j 2
  have hg6 (j : ℕ) : (∫ ω, (G j ω) ^ 6 ∂P) = 15 := by
    simpa using hGmom j 3
  have hg8 (j : ℕ) : (∫ ω, (G j ω) ^ 8 ∂P) = 105 := by
    simpa using hGmom j 4
  have hgint (j n : ℕ) : Integrable (fun ω => (G j ω) ^ n) P :=
    hpow n (hLp j n)
  have hmean (j : ℕ) : (∫ ω, F j ω ∂P) = 0 := by
    dsimp [F]
    rw [integral_const_mul, integral_sub (hgint j 2) (integrable_const 1), hg2]
    simp
  have hsecond (j : ℕ) : (∫ ω, (F j ω) ^ 2 ∂P) = 2 * (a j) ^ 2 := by
    have heq : (fun ω => (F j ω) ^ 2) =
        fun ω => (a j) ^ 2 * ((G j ω) ^ 4 - 2 * (G j ω) ^ 2 + 1) := by
      funext ω; dsimp [F]; ring
    rw [heq, integral_const_mul, integral_add, integral_sub, integral_const_mul, hg4, hg2]
    · simp; ring
    · exact hgint j 4
    · exact (hgint j 2).const_mul 2
    · exact (hgint j 4).sub ((hgint j 2).const_mul 2)
    · exact integrable_const 1
  have hfourth (j : ℕ) : (∫ ω, (F j ω) ^ 4 ∂P) = 60 * (a j) ^ 4 := by
    have heq : (fun ω => (F j ω) ^ 4) =
        fun ω => (a j) ^ 4 * ((G j ω) ^ 8 - 4 * (G j ω) ^ 6 +
          6 * (G j ω) ^ 4 - 4 * (G j ω) ^ 2 + 1) := by
      funext ω; dsimp [F]; ring
    rw [heq, integral_const_mul, integral_add, integral_sub, integral_add, integral_sub]
    · simp only [integral_const_mul, hg8, hg6, hg4, hg2, integral_const,
        probReal_univ, smul_eq_mul, one_mul]
      ring
    · exact hgint j 8
    · exact (hgint j 6).const_mul 4
    · exact (hgint j 8).sub ((hgint j 6).const_mul 4)
    · exact (hgint j 4).const_mul 6
    · exact ((hgint j 8).sub ((hgint j 6).const_mul 4)).add ((hgint j 4).const_mul 6)
    · exact (hgint j 2).const_mul 4
    · exact (((hgint j 8).sub ((hgint j 6).const_mul 4)).add
        ((hgint j 4).const_mul 6)).sub ((hgint j 2).const_mul 4)
    · exact integrable_const 1
  let T (s : Finset ℕ) (ω : Ω) : ℝ := ∑ j ∈ s, F j ω
  have hT (s : Finset ℕ) (p : ℝ≥0) : MemLp (T s) p P :=
    memLp_finsetSum s (fun j _ => hF j p)
  have hTint (s : Finset ℕ) (n : ℕ) : Integrable (fun ω => (T s ω) ^ n) P :=
    hpow n (hT s n)
  have hFint (j n : ℕ) : Integrable (fun ω => (F j ω) ^ n) P :=
    hpow n (hF j n)
  have hTmean (s : Finset ℕ) : (∫ ω, T s ω ∂P) = 0 := by
    rw [show T s = (fun ω => ∑ j ∈ s, F j ω) from rfl,
      integral_finsetSum s (fun j _ => (hF j 1).integrable (by norm_num))]
    simp [hmean]
  have hindF : iIndepFun F P := hind.comp (fun j x => a j * (x ^ 2 - 1))
    (fun _ => by fun_prop)
  have hfinite (s : Finset ℕ) :
      (∫ ω, (T s ω) ^ 2 ∂P) = 2 * ∑ j ∈ s, (a j) ^ 2 ∧
      (∫ ω, (T s ω) ^ 4 ∂P) =
        12 * (∑ j ∈ s, (a j) ^ 2) ^ 2 + 48 * ∑ j ∈ s, (a j) ^ 4 := by
    induction s using Finset.induction_on with
    | empty => simp [T]
    | @insert i s hi ih =>
      have hiind : IndepFun (T s) (F i) P := by
        convert hindF.indepFun_finsetSum_of_notMem₀
          (fun j => (hF j 1).aemeasurable) hi using 1
        ext ω
        simp [T]
      have hindpow (r t : ℕ) :
          IndepFun (fun ω => (T s ω) ^ r) (fun ω => (F i ω) ^ t) P :=
        hiind.comp (measurable_id.pow_const r) (measurable_id.pow_const t)
      have hI (r t : ℕ) : Integrable (fun ω => (T s ω) ^ r * (F i ω) ^ t) P :=
        (hindpow r t).integrable_mul (hTint s r) (hFint i t)
      have hE (r t : ℕ) :
          (∫ ω, (T s ω) ^ r * (F i ω) ^ t ∂P) =
          (∫ ω, (T s ω) ^ r ∂P) * (∫ ω, (F i ω) ^ t ∂P) :=
        (hindpow r t).integral_mul_eq_mul_integral (hTint s r).aestronglyMeasurable
          (hFint i t).aestronglyMeasurable
      have hins (ω : Ω) : T (insert i s) ω = T s ω + F i ω := by
        simp [T, Finset.sum_insert hi, add_comm]
      constructor
      · have heq : (fun ω => (T (insert i s) ω) ^ 2) =
            fun ω => (T s ω) ^ 2 + 2 * ((T s ω) ^ 1 * (F i ω) ^ 1) + (F i ω) ^ 2 := by
          funext ω; rw [hins]; ring
        rw [heq, integral_add, integral_add, integral_const_mul, hE,
          ih.1, hsecond]
        · simp only [pow_one, hTmean, hmean, mul_zero, add_zero,
            Finset.sum_insert hi]
          ring
        · exact hTint s 2
        · exact (hI 1 1).const_mul 2
        · exact (hTint s 2).add ((hI 1 1).const_mul 2)
        · exact hFint i 2
      · have heq : (fun ω => (T (insert i s) ω) ^ 4) =
            fun ω => (T s ω) ^ 4 + 4 * ((T s ω) ^ 3 * (F i ω) ^ 1) +
              6 * ((T s ω) ^ 2 * (F i ω) ^ 2) +
              4 * ((T s ω) ^ 1 * (F i ω) ^ 3) + (F i ω) ^ 4 := by
          funext ω; rw [hins]; ring
        rw [heq, integral_add, integral_add, integral_add, integral_add]
        · simp only [integral_const_mul]
          rw [hE 3 1, hE 2 2, hE 1 3]
          simp only [pow_one, hmean, hTmean,
            mul_zero, zero_mul, add_zero, ih.1, ih.2, hsecond, hfourth,
            Finset.sum_insert hi]
          ring
        · exact hTint s 4
        · exact (hI 3 1).const_mul 4
        · exact (hTint s 4).add ((hI 3 1).const_mul 4)
        · exact (hI 2 2).const_mul 6
        · exact ((hTint s 4).add ((hI 3 1).const_mul 4)).add ((hI 2 2).const_mul 6)
        · exact (hI 1 3).const_mul 4
        · exact (((hTint s 4).add ((hI 3 1).const_mul 4)).add
            ((hI 2 2).const_mul 6)).add ((hI 1 3).const_mul 4)
        · exact hFint i 4
  have hnorm (n : ℕ) (hn : n ≠ 0) (f : Ω → ℝ) (hf : MemLp f n P) :
      (eLpNorm f n P).toReal ^ n = ∫ ω, ‖f ω‖ ^ n ∂P := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hn) (by simp)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact Real.rpow_inv_natCast_pow (integral_nonneg (fun _ => by positivity)) hn
  have hnorm4 (f : Ω → ℝ) (hf : MemLp f 4 P) :
      (eLpNorm f 4 P).toReal ^ 4 = ∫ ω, f ω ^ 4 ∂P := by
    have heq (x : ℝ) : ‖x‖ ^ 4 = x ^ 4 := by
      simp only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
    simpa only [Nat.cast_ofNat, heq] using hnorm 4 (by norm_num) f hf
  let Z (j : ℕ) : Lp ℝ 4 P := (hF j 4).toLp (F j)
  have hZ (s : Finset ℕ) : ⇑(∑ j ∈ s, Z j) =ᵐ[P] T s := by
    refine (Lp.coeFn_fun_finsetSum s Z).trans ?_
    have h := ae_all_iff.mpr (fun j => (hF j 4).coeFn_toLp)
    filter_upwards [h] with ω hω
    exact Finset.sum_congr rfl (fun j _ => hω j)
  have hZnorm (s : Finset ℕ) : ‖∑ j ∈ s, Z j‖ ^ 4 =
      12 * (∑ j ∈ s, a j ^ 2) ^ 2 + 48 * ∑ j ∈ s, a j ^ 4 := by
    rw [Lp.norm_def, eLpNorm_congr_ae (hZ s), hnorm4 _ (hT s 4)]
    exact (hfinite s).2
  have hfinitebound (s : Finset ℕ) :
      ∑ j ∈ s, a j ^ 4 ≤ (∑ j ∈ s, a j ^ 2) ^ 2 := by
    simpa only [← pow_mul] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := s) (fun j _ => sq_nonneg (a j))
  have hZbound (s : Finset ℕ) :
      ‖∑ j ∈ s, Z j‖ ^ 4 ≤ 60 * (∑ j ∈ s, a j ^ 2) ^ 2 := by
    rw [hZnorm]
    nlinarith [hfinitebound s]
  have hZsum : Summable Z := by
    apply summable_iff_vanishing_norm.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp ha (ε ^ 2 / 60) (by positivity)
    refine ⟨s, fun t ht => ?_⟩
    have ht0 : 0 ≤ ∑ j ∈ t, a j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have htε : (∑ j ∈ t, a j ^ 2) < ε ^ 2 / 60 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg ht0] using hs t ht
    have hb := hZbound t
    have hp : (∑ j ∈ t, a j ^ 2) ^ 2 < (ε ^ 2 / 60) ^ 2 :=
      pow_lt_pow_left₀ htε ht0 (by norm_num)
    have hε4 : 0 < ε ^ 4 := by positivity
    have hn : 0 ≤ ‖∑ j ∈ t, Z j‖ := norm_nonneg _
    by_contra hc
    have hle := pow_le_pow_left₀ (le_of_lt hε) (le_of_not_gt hc) 4
    nlinarith
  let X : Lp ℝ 4 P := ∑' j, Z j
  have hlim : Tendsto (fun s : Finset ℕ => ∑ j ∈ s, Z j) atTop (𝓝 X) := hZsum.hasSum
  have hL4 : Tendsto (fun s : Finset ℕ => eLpNorm (T s - ⇑X) 4 P) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ X).mp hlim
    exact h.congr (fun s => eLpNorm_congr_ae ((hZ s).sub EventuallyEq.rfl))
  have hLq (q : ℝ≥0∞) (hq : q ≤ 4) :
      Tendsto (fun s : Finset ℕ => eLpNorm (T s - ⇑X) q P) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL4
      (fun _ => bot_le) (fun s => eLpNorm_le_eLpNorm_of_exponent_le hq
        ((hT s 4).aestronglyMeasurable.sub (Lp.memLp X).aestronglyMeasurable))
  have hX2 : MemLp (⇑X) 2 P := (Lp.memLp X).mono_exponent (by norm_num)
  have hXmean : (∫ ω, X ω ∂P) = 0 := by
    have h := tendsto_integral_of_L1' (⇑X) (Lp.memLp X).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => (hT s 1).integrable (by norm_num)))
      (hLq 1 (by norm_num))
    simp only [hTmean] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hnorm2 (f : Ω → ℝ) (hf : MemLp f 2 P) :
      (eLpNorm f 2 P).toReal ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs, sq_abs] using hnorm 2 (by norm_num) f hf
  have hXsecond : (∫ ω, X ω ^ 2 ∂P) = 2 * ∑' j, a j ^ 2 := by
    have hT2 (s : Finset ℕ) : MemLp (T s) (2 : ℝ≥0∞) P := hT s 2
    have hnT (s : Finset ℕ) : ‖(hT2 s).toLp (T s)‖ ^ 2 = 2 * ∑ j ∈ s, a j ^ 2 := by
      rw [Lp.norm_toLp, hnorm2 _ (hT2 s)]
      exact (hfinite s).1
    have h := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' T hT2 (⇑X) hX2).mpr
      (hLq 2 (by norm_num))).norm.pow 2
    simp only [hnT] at h
    rw [Lp.norm_toLp, hnorm2 _ hX2] at h
    exact tendsto_nhds_unique h (tendsto_const_nhds.mul ha.hasSum)
  have ha4 : Summable (fun j => a j ^ 4) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ (ha.mul_left (∑' j, a j ^ 2))
    intro j
    have hle : a j ^ 2 ≤ ∑' k, a k ^ 2 := ha.le_tsum j (fun _ _ => sq_nonneg _)
    nlinarith [sq_nonneg (a j)]
  have hXfourth : (∫ ω, X ω ^ 4 ∂P) =
      12 * (∑' j, a j ^ 2) ^ 2 + 48 * ∑' j, a j ^ 4 := by
    have h := hlim.norm.pow 4
    simp only [hZnorm] at h
    rw [Lp.norm_def, hnorm4 _ (Lp.memLp X)] at h
    exact tendsto_nhds_unique h
      ((tendsto_const_nhds.mul (ha.hasSum.pow 2)).add (tendsto_const_nhds.mul ha4.hasSum))
  have ha4bound : (∑' j, a j ^ 4) ≤ (∑' j, a j ^ 2) ^ 2 :=
    le_of_tendsto_of_tendsto' ha4.hasSum (ha.hasSum.pow 2) hfinitebound
  refine ⟨fun j => hF j 4, X, hZsum.hasSum, hX2, hLq 2 (by norm_num),
    hXmean, hXsecond, hXfourth, ?_⟩
  rw [hXfourth, hXsecond]
  nlinarith

end D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment
