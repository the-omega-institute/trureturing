/- GID: D5/S3/Analytic/Oscillation/OrdinateCounting
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/OrdinateCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic counting growth controls triangular mass and selects substantial upper bands. -/

import D5.S3.Analytic.Fourier.AngularFejerKernel
import D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness

/-! Weighted counting and triangular localization of a locally finite positive spectrum. -/

namespace D5.S3.Analytic.Oscillation.OrdinateCounting

open D5.S3.Analytic.Fourier.AngularFejerKernel (phi phi_eq_zero phi_continuous)
open Set Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

structure Spectrum where
  index : Type
  gamma : index → ℝ
  mult : index → ℕ
  gamma_pos : ∀ j, 0 < gamma j
  gamma_injective : Function.Injective gamma
  mult_pos : ∀ j, 0 < mult j
  finite_le : ∀ T : ℝ, {j | gamma j ≤ T}.Finite

noncomputable def Spectrum.cut (S : Spectrum) (T : ℝ) : Finset S.index :=
  (S.finite_le T).toFinset

noncomputable def Spectrum.N (S : Spectrum) (T : ℝ) : ℕ :=
  ∑ j ∈ S.cut T, S.mult j

def CountAsymptotic (S : Spectrum) : Prop :=
  Tendsto (fun T : ℝ => (S.N T : ℝ) / (T * Real.log T))
    atTop (nhds (1 / (2 * Real.pi)))

noncomputable def Wminus (S : Spectrum) (M : ℝ) : ℝ :=
  ∑ j ∈ S.cut M, (S.mult j : ℝ) * phi M (S.gamma j)

noncomputable def Wplus (S : Spectrum) (b U : ℝ) : ℝ :=
  ∑ j ∈ S.cut (U + b), (S.mult j : ℝ) * phi b (S.gamma j - U)

noncomputable def windowMass (S : Spectrum) (b U : ℝ) : ℕ := by
  classical
  exact ∑ j ∈ S.cut (U + b), if |S.gamma j - U| < b then S.mult j else 0

/-- A locally finite positive spectrum is separated from zero. -/
theorem positive_gap (S : Spectrum) : ∃ b : ℝ, 0 < b ∧ ∀ j, b < S.gamma j := by
  classical
  have hfinite (s : Finset S.index) :
      ∃ b : ℝ, 0 < b ∧ ∀ j ∈ s, b < S.gamma j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert j s _ ih =>
      obtain ⟨b, hb, hbs⟩ := ih
      refine ⟨min b (S.gamma j / 2), lt_min hb (div_pos (S.gamma_pos j) (by norm_num)), ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (min_le_right _ _).trans_lt (by linarith [S.gamma_pos k])
      · exact (min_le_left _ _).trans_lt (hbs k hk)
  obtain ⟨b, hb, hbs⟩ := hfinite (S.cut 1)
  refine ⟨min b (1 / 2), lt_min hb (by norm_num), ?_⟩
  intro j
  by_cases hj : S.gamma j ≤ 1
  · exact (min_le_left _ _).trans_lt (hbs j (by simpa [Spectrum.cut] using hj))
  · exact (min_le_right _ _).trans_lt (by linarith)

private lemma count_mono (S : Spectrum) : Monotone (fun t => (S.N t : ℝ)) := by
  classical
  intro u v huv
  change (S.N u : ℝ) ≤ (S.N v : ℝ)
  apply Nat.cast_le.mpr
  exact Finset.sum_le_sum_of_subset (f := S.mult) (show S.cut u ⊆ S.cut v from by
    intro j hj
    simpa only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (show S.gamma j ≤ u from by simpa [Spectrum.cut] using hj).trans huv)

/-- Logarithmic counting growth gives a uniform inverse-square tail bound. -/
theorem inverse_square_tail (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      Summable (fun j : {j : S.index // T < S.gamma j} => (S.mult j.val : ℝ) / (S.gamma j.val) ^ 2) ∧
      (∑' j : {j : S.index // T < S.gamma j}, (S.mult j.val : ℝ) / (S.gamma j.val) ^ 2)
        ≤ C * Real.log T / T := by
  classical
  let c : ℝ := 1 / (2 * Real.pi) + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hevent : ∀ᶠ u : ℝ in atTop,
      (S.N u : ℝ) / (u * Real.log u) < c :=
    hN.eventually (gt_mem_nhds (by dsimp [c]; linarith))
  obtain ⟨A, hA⟩ := eventually_atTop.1 hevent
  let L : ℝ := max A 4
  let B : ℝ := S.N L
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hcount (u : ℝ) (hu : 4 ≤ u) :
      (S.N u : ℝ) ≤ c * u * Real.log u + B * u := by
    have hu0 : 0 < u := by linarith
    have hlog : 0 ≤ Real.log u := (Real.log_pos (by linarith)).le
    by_cases hLu : L ≤ u
    · have hb := (div_lt_iff₀ (mul_pos hu0 (Real.log_pos (by linarith)))).mp
        (hA u ((le_max_left A 4).trans hLu))
      have : 0 ≤ B * u := mul_nonneg hB hu0.le
      nlinarith [hb]
    · have hb : (S.N u : ℝ) ≤ B := count_mono S (le_of_not_ge hLu)
      have hb' : B ≤ B * u := le_mul_of_one_le_right hB (by linarith)
      have : 0 ≤ c * u * Real.log u := mul_nonneg (mul_nonneg hc hu0.le) hlog
      linarith
  let hfinite : ∀ u : ℝ, Set.Finite {j | S.gamma j < u} :=
    fun u => (S.finite_le u).subset (fun j (hj : S.gamma j < u) =>
      show S.gamma j ≤ u from hj.le)
  have hstrict (u : ℝ) :
      D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness.strictCount
        S.gamma (fun j => (S.mult j : ℝ)) hfinite u ≤ (S.N u : ℝ) := by
    unfold D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness.strictCount
    rw [Spectrum.N, Nat.cast_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness.realCutoff,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hj
      simpa only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hj.le
    · intro j _ _
      exact Nat.cast_nonneg _
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  let K : ℝ := 2 * (c + (c + B) / Real.log 4)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hfinitebound (s : Finset {j : S.index // T < S.gamma j}) :
      ∑ j ∈ s, (S.mult j.val : ℝ) / (S.gamma j.val)^2 ≤
        2 * (c * (Real.log T + 1) + B) / T := by
    have h := D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness.finite_high_inverse_square_bound
      (s.image Subtype.val) S.gamma (fun j => (S.mult j : ℝ)) hfinite
      (L := 4) (by norm_num) hT (fun _ => Nat.cast_nonneg _) hc hB
      (by
        intro j hj
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
        exact k.property.le)
      (fun u hu => (hstrict u).trans (hcount u hu))
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at h
    exact h
  have hnonneg (j : {j : S.index // T < S.gamma j}) :
      0 ≤ (S.mult j.val : ℝ) / (S.gamma j.val)^2 := by positivity
  refine ⟨summable_of_sum_le hnonneg hfinitebound,
    (Real.tsum_le_of_sum_le hnonneg hfinitebound).trans ?_⟩
  apply (div_le_div_iff_of_pos_right hT0).mpr
  have hlog : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hb : c + B ≤ (c + B) / Real.log 4 * Real.log T := by
    calc
      c + B = (c + B) / Real.log 4 * Real.log 4 := by field_simp
      _ ≤ (c + B) / Real.log 4 * Real.log T :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  dsimp [K]
  nlinarith

private lemma triangular_integral (S : Spectrum) {M : ℝ} (hM : 0 < M) :
    Wminus S M = ∫ u in Ioc (0 : ℝ) 1, (S.N (M * u) : ℝ) := by
  classical
  let k (j : S.index) : ℝ → ℝ :=
    (Icc (S.gamma j / M) 1).indicator (fun _ => (S.mult j : ℝ))
  have hk (j : S.index) : IntegrableOn (k j) (Ioc (0 : ℝ) 1) :=
    (integrableOn_const (C := (S.mult j : ℝ)) (by simp)).indicator measurableSet_Icc
  have heach (j : S.index) (hj : j ∈ S.cut M) :
      (∫ u in Ioc (0 : ℝ) 1, k j u) = (S.mult j : ℝ) * phi M (S.gamma j) := by
    have hjM : S.gamma j ≤ M := by simpa [Spectrum.cut] using hj
    have ha : 0 < S.gamma j / M := div_pos (S.gamma_pos j) hM
    have ha1 : S.gamma j / M ≤ 1 := (div_le_one hM).mpr hjM
    have hsub : Icc (S.gamma j / M) 1 ⊆ Ioc (0 : ℝ) 1 :=
      fun _ hx => ⟨ha.trans_le hx.1, hx.2⟩
    dsimp only [k]
    rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub,
      setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ha1), smul_eq_mul]
    rw [phi, abs_of_pos (S.gamma_pos j), max_eq_right (sub_nonneg.mpr ha1)]
    ring
  have hsum (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) :
      (S.N (M * u) : ℝ) = ∑ j ∈ S.cut M, k j u := by
    have hMu : M * u ≤ M := by nlinarith [hu.2]
    rw [Spectrum.N, Nat.cast_sum]
    have hsub : S.cut (M * u) ⊆ S.cut M := by
      intro j hj
      simpa only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
        (show S.gamma j ≤ M * u from by simpa [Spectrum.cut] using hj).trans hMu
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : S.gamma j ≤ M * u := by simpa [Spectrum.cut] using hj
      exact (indicator_of_mem
        (show u ∈ Icc (S.gamma j / M) 1 from
          ⟨(div_le_iff₀ hM).mpr (by nlinarith), hu.2⟩)
        (fun _ : ℝ => (S.mult j : ℝ))).symm
    · intro j _ hj
      have hj' : ¬ S.gamma j ≤ M * u := by simpa [Spectrum.cut] using hj
      apply indicator_of_notMem
      intro hjmem
      exact hj' (by have := (div_le_iff₀ hM).mp hjmem.1; nlinarith)
  rw [setIntegral_congr_fun measurableSet_Ioc hsum,
    integral_finsetSum _ (fun j _ => hk j)]
  exact (Finset.sum_congr rfl heach).symm

private lemma count_scaled_limit (S : Spectrum) (hN : CountAsymptotic S)
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun M : ℝ => (S.N (M * u) : ℝ) / (M * Real.log M))
      atTop (nhds ((1 / (2 * Real.pi)) * u)) := by
  have hMu : Tendsto (fun M : ℝ => M * u) atTop atTop :=
    tendsto_id.atTop_mul_const hu
  have hratio : Tendsto (fun M : ℝ => u * (1 + Real.log u / Real.log M))
      atTop (nhds u) := by
    have hz : Tendsto (fun M : ℝ => Real.log u / Real.log M) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using ((tendsto_inv_atTop_zero.comp
        Real.tendsto_log_atTop).const_mul (Real.log u))
    simpa only [add_zero, mul_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add hz).const_mul u
  have ht := (hN.comp hMu).mul hratio
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hMu.eventually (eventually_gt_atTop 1)]
    with M hM hMu1
  dsimp only [Function.comp_def]
  rw [Real.log_mul (by linarith : M ≠ 0) hu.ne']
  have hlog : Real.log M ≠ 0 := (Real.log_pos hM).ne'
  have hM0 : M ≠ 0 := by linarith
  have hMuLog : Real.log M + Real.log u ≠ 0 := by
    rw [← Real.log_mul hM0 hu.ne']
    exact (Real.log_pos hMu1).ne'
  field_simp [hlog, hM0, hu.ne', hMuLog]

/-- The triangularly weighted lower count has half the leading counting constant. -/
theorem lower_triangular_mass (S : Spectrum) (hN : CountAsymptotic S) :
    Tendsto (fun M : ℝ => Wminus S M / (M * Real.log M))
      atTop (nhds (1 / (4 * Real.pi))) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let F : ℝ → ℝ → ℝ := fun M u => (S.N (M * u) : ℝ) / (M * Real.log M)
  have hmono := count_mono S
  have hmeas (M : ℝ) : Measurable (F M) :=
    (hmono.measurable.comp (measurable_const.mul measurable_id)).div_const _
  have hbound : ∀ᶠ M : ℝ in atTop,
      ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1), ‖F M u‖ ≤ c + 1 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      (show Tendsto _ atTop (nhds c) from hN).eventually (gt_mem_nhds (by linarith : c < c + 1))]
      with M hM hc
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro u hu
    have hden : 0 < M * Real.log M := mul_pos (by linarith) (Real.log_pos (by linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity)]
    exact (div_le_div_of_nonneg_right (hmono (by nlinarith [hu.2])) hden.le).trans hc.le
  have hlim : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun M => F M u) atTop (nhds (c * u)) := by
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro u hu
    exact count_scaled_limit S hN hu.1
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ => c + 1) (Eventually.of_forall (fun M => (hmeas M).aestronglyMeasurable))
    hbound (integrableOn_const (C := c + 1) (by simp)) hlim
  have hint : (∫ u in Ioc (0 : ℝ) 1, c * u) = 1 / (4 * Real.pi) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul, integral_id]
    dsimp [c]
    ring
  rw [hint] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  rw [triangular_integral S hM, ← integral_div]

private lemma localized_sums (S : Spectrum) {b U R : ℝ} (hb : 0 < b)
    (hR : U + b ≤ R) :
    Wplus S b U = ∑ j ∈ S.cut R, (S.mult j : ℝ) * phi b (S.gamma j - U) ∧
    (windowMass S b U : ℝ) =
      ∑ j ∈ S.cut R, if |S.gamma j - U| < b then (S.mult j : ℝ) else 0 := by
  classical
  have hsub : S.cut (U + b) ⊆ S.cut R := by
    intro j hj
    simpa only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (show S.gamma j ≤ U + b from by simpa [Spectrum.cut] using hj).trans hR
  have hout (j : S.index) (hj : j ∉ S.cut (U + b)) : b ≤ |S.gamma j - U| := by
    have hj' : ¬ S.gamma j ≤ U + b := by simpa [Spectrum.cut] using hj
    exact le_trans (by linarith) (le_abs_self _)
  constructor
  · exact Finset.sum_subset hsub (fun j _ hj => by
      rw [phi_eq_zero hb (hout j hj), mul_zero])
  · simp only [windowMass, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    exact Finset.sum_subset hsub (fun j _ hj => ite_eq_right (not_lt.mpr (hout j hj)))

private lemma window_kernel (b g : ℝ) :
    (fun U : ℝ => if |g - U| < b then (1 : ℝ) else 0) =
      (Ioo (g - b) (g + b)).indicator (fun _ => (1 : ℝ)) := by
  funext U
  have hiff : |g - U| < b ↔ U ∈ Ioo (g - b) (g + b) := by
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [hiff, indicator_apply]

private lemma window_integrable (b g a d : ℝ) :
    IntegrableOn (fun U : ℝ => if |g - U| < b then (1 : ℝ) else 0) (Icc a d) := by
  rw [window_kernel]
  exact (integrableOn_const (C := (1 : ℝ)) (by simp)).indicator measurableSet_Ioo

private lemma window_integral_bound {b : ℝ} (hb : 0 < b) (g a d : ℝ) :
    (∫ U in Icc a d, if |g - U| < b then (1 : ℝ) else 0) ≤ 2 * b := by
  rw [window_kernel]
  have hi : Integrable ((Ioo (g - b) (g + b)).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (by simp)).integrable_indicator measurableSet_Ioo
  have hn : ∀ U : ℝ, 0 ≤ (Ioo (g - b) (g + b)).indicator (fun _ => (1 : ℝ)) U := by
    intro U
    simp only [indicator_apply]
    split_ifs <;> norm_num
  have hh := setIntegral_le_integral (s := Icc a d) hi (Eventually.of_forall hn)
  simpa [integral_indicator_const, Measure.real, Real.volume_Ioo,
    hb.le, show 0 ≤ g + b - (g - b) by linarith,
    show g + b - (g - b) = 2 * b by ring] using hh

private lemma phi_integral_lower {b g a d : ℝ} (hb : 0 < b)
    (hga : a ≤ g - b / 2) (hgd : g + b / 2 ≤ d) :
    b / 2 ≤ ∫ U in Icc a d, phi b (g - U) := by
  have hphi : Continuous (fun U : ℝ => phi b (g - U)) :=
    (phi_continuous b).comp (continuous_const.sub continuous_id)
  have hi : IntegrableOn (fun U : ℝ => phi b (g - U)) (Icc a d) :=
    hphi.integrableOn_Icc
  have hsub : Icc (g - b / 2) (g + b / 2) ⊆ Icc a d :=
    fun U hU => ⟨hga.trans hU.1, hU.2.trans hgd⟩
  have hm := setIntegral_mono_set hi
    (Eventually.of_forall (fun U => le_max_left (0 : ℝ) _))
    (Eventually.of_forall hsub)
  have hl : (∫ _U in Icc (g - b / 2) (g + b / 2), (1 / 2 : ℝ)) ≤
      ∫ U in Icc (g - b / 2) (g + b / 2), phi b (g - U) := by
    apply setIntegral_mono_on (integrableOn_const (by simp))
      (hphi.continuousOn.integrableOn_Icc) measurableSet_Icc
    intro U hU
    apply le_trans _ (le_max_right _ _)
    have ha : |g - U| ≤ b / 2 := abs_le.mpr ⟨by linarith [hU.2], by linarith [hU.1]⟩
    have hd := (div_le_iff₀ hb).mpr (show |g - U| ≤ (1 / 2) * b by linarith)
    linarith
  have heq : (∫ _U in Icc (g - b / 2) (g + b / 2), (1 / 2 : ℝ)) = b / 2 := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  exact heq.symm.trans_le (hl.trans hm)

/-- Some band has logarithmic triangular mass and counting mass at most twelve
times its triangular mass. -/
theorem select_upper_band (S : Spectrum) (hN : CountAsymptotic S) {b : ℝ} (hb : 0 < b) :
    ∃ cb : ℝ, 0 < cb ∧ ∀ᶠ T : ℝ in atTop,
      ∃ U ∈ Icc T (2 * T),
        (windowMass S b U : ℝ) ≤ 12 * Wplus S b U ∧
          cb * Real.log T ≤ Wplus S b U := by
  classical
  let c : ℝ := 1 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlowlim := (count_scaled_limit S hN (u := 31 / 16) (by norm_num)).sub
    (count_scaled_limit S hN (u := 17 / 16) (by norm_num))
  have hupperlim := count_scaled_limit S hN (u := 17 / 8) (by norm_num)
  have hlow : ∀ᶠ T : ℝ in atTop,
      (4 / 5) * c * (T * Real.log T) ≤
        (S.N (T * (31 / 16)) : ℝ) - (S.N (T * (17 / 16)) : ℝ) := by
    have hh := hlowlim.eventually (lt_mem_nhds
      (show (4 / 5) * c < c * (31 / 16) - c * (17 / 16) by nlinarith))
    filter_upwards [hh, eventually_gt_atTop (1 : ℝ)] with T hT hT1
    have hd : 0 < T * Real.log T := mul_pos (by linarith) (Real.log_pos hT1)
    rw [← sub_div] at hT
    exact (le_div_iff₀ hd).mp hT.le
  have hupper : ∀ᶠ T : ℝ in atTop,
      (S.N (T * (17 / 8)) : ℝ) ≤ (9 / 4) * c * (T * Real.log T) := by
    have hh := hupperlim.eventually (gt_mem_nhds
      (show c * (17 / 8) < (9 / 4) * c by nlinarith))
    filter_upwards [hh, eventually_gt_atTop (1 : ℝ)] with T hT hT1
    exact (div_le_iff₀ (mul_pos (by linarith) (Real.log_pos hT1))).mp hT.le
  refine ⟨b * c / 100, by positivity, ?_⟩
  filter_upwards [hlow, hupper, eventually_ge_atTop (8 * b),
    eventually_gt_atTop (1 : ℝ)] with T hl hu hTb hT1
  have hT : 0 < T := by linarith
  let s := S.cut (T * (17 / 8))
  let core := S.cut (T * (31 / 16)) \ S.cut (T * (17 / 16))
  let w : ℝ → ℝ := fun U => ∑ j ∈ s, (S.mult j : ℝ) * phi b (S.gamma j - U)
  let n : ℝ → ℝ := fun U =>
    ∑ j ∈ s, if |S.gamma j - U| < b then (S.mult j : ℝ) else 0
  have hphi (j : S.index) : Continuous (fun U : ℝ => phi b (S.gamma j - U)) :=
    (phi_continuous b).comp (continuous_const.sub continuous_id)
  have hwint : IntegrableOn w (Icc T (2 * T)) := by
    apply integrable_finsetSum
    intro j _
    exact ((hphi j).const_mul (S.mult j : ℝ)).integrableOn_Icc
  have hnterm (j : S.index) :
      IntegrableOn (fun U : ℝ => if |S.gamma j - U| < b then (S.mult j : ℝ) else 0)
        (Icc T (2 * T)) := by
    simpa only [IntegrableOn, mul_ite, mul_one, mul_zero] using
      (window_integrable b (S.gamma j) T (2 * T)).const_mul (S.mult j : ℝ)
  have hnint : IntegrableOn n (Icc T (2 * T)) :=
    integrable_finsetSum s (fun j _ => hnterm j)
  have hnub : (∫ U in Icc T (2 * T), n U) ≤
      (9 / 2) * b * c * (T * Real.log T) := by
    calc
      _ = ∑ j ∈ s, (S.mult j : ℝ) *
          (∫ U in Icc T (2 * T), if |S.gamma j - U| < b then (1 : ℝ) else 0) := by
        rw [integral_finsetSum s (fun j _ => hnterm j)]
        apply Finset.sum_congr rfl
        intro j _
        rw [← integral_const_mul]
        congr 1
        funext U
        split_ifs <;> simp
      _ ≤ ∑ j ∈ s, (S.mult j : ℝ) * (2 * b) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (window_integral_bound hb _ _ _) (Nat.cast_nonneg _)
      _ = 2 * b * (S.N (T * (17 / 8)) : ℝ) := by
        rw [← Finset.sum_mul]
        simp only [Spectrum.N, Nat.cast_sum, s]
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * b)]
  have hcutmono {x y : ℝ} (hxy : x ≤ y) : S.cut x ⊆ S.cut y := by
    intro j hj
    simpa only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (show S.gamma j ≤ x from by simpa [Spectrum.cut] using hj).trans hxy
  have hcoresub : core ⊆ s := by
    intro j hj
    exact hcutmono (by nlinarith : T * (31 / 16) ≤ T * (17 / 8))
      (Finset.mem_sdiff.mp hj).1
  have hcorecount : (∑ j ∈ core, (S.mult j : ℝ)) =
      (S.N (T * (31 / 16)) : ℝ) - (S.N (T * (17 / 16)) : ℝ) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [Spectrum.N, Nat.cast_sum] using
      (Finset.sum_sdiff (f := fun j => (S.mult j : ℝ))
        (hcutmono (by nlinarith : T * (17 / 16) ≤ T * (31 / 16))))
  have hwlower : (2 / 5) * b * c * (T * Real.log T) ≤
      ∫ U in Icc T (2 * T), w U := by
    calc
      _ ≤ b / 2 * ((S.N (T * (31 / 16)) : ℝ) - (S.N (T * (17 / 16)) : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ b / 2)]
      _ = ∑ j ∈ core, (S.mult j : ℝ) * (b / 2) := by
        rw [← hcorecount, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j ∈ core, (S.mult j : ℝ) *
          (∫ U in Icc T (2 * T), phi b (S.gamma j - U)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : S.gamma j ≤ T * (31 / 16) ∧ ¬ S.gamma j ≤ T * (17 / 16) := by
          simpa [core, Spectrum.cut] using hj
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact phi_integral_lower hb (by nlinarith [hj'.2]) (by nlinarith [hj'.1])
      _ ≤ ∑ j ∈ s, (S.mult j : ℝ) *
          (∫ U in Icc T (2 * T), phi b (S.gamma j - U)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hcoresub
        intro j _ _
        exact mul_nonneg (Nat.cast_nonneg _)
          (integral_nonneg (fun _ => le_max_left (0 : ℝ) _))
      _ = ∫ U in Icc T (2 * T), w U := by
        rw [integral_finsetSum s (fun j _ =>
          ((hphi j).const_mul (S.mult j : ℝ)).integrableOn_Icc)]
        simp only [integral_const_mul]
  have hex : ∃ U ∈ Icc T (2 * T),
      n U ≤ 12 * w U ∧ (b * c / 100) * Real.log T ≤ w U := by
    by_contra hno
    push Not at hno
    have hn0 (U : ℝ) : 0 ≤ n U := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs <;> positivity
    have hpoint (U : ℝ) (hU : U ∈ Icc T (2 * T)) :
        w U ≤ n U / 12 + (b * c / 100) * Real.log T := by
      have hq : 0 ≤ (b * c / 100) * Real.log T := by
        exact mul_nonneg (by positivity) (Real.log_pos hT1).le
      by_cases hgood : n U ≤ 12 * w U
      · have hh := hno U hU hgood
        linarith [hn0 U]
      · push Not at hgood
        linarith
    have hi := setIntegral_mono_on hwint
      ((hnint.div_const 12).add (integrableOn_const (by simp))) measurableSet_Icc hpoint
    dsimp only [Pi.add_apply] at hi
    rw [integral_add (hnint.div_const 12) (integrableOn_const (by simp)),
      integral_div, setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * T - T), smul_eq_mul] at hi
    have hpos : 0 < b * c * (T * Real.log T) :=
      mul_pos (mul_pos hb hc) (mul_pos hT (Real.log_pos hT1))
    nlinarith
  obtain ⟨U, hU, hn, hw⟩ := hex
  have heq := localized_sums S hb (U := U) (R := T * (17 / 8)) (by nlinarith [hU.2])
  exact ⟨U, hU, by simpa only [heq.1, heq.2] using hn,
    by simpa only [heq.1] using hw⟩

#print axioms positive_gap
#print axioms lower_triangular_mass
#print axioms select_upper_band

end
end D5.S3.Analytic.Oscillation.OrdinateCounting
