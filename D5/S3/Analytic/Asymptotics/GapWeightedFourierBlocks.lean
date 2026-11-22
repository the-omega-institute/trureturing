/- GID: D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/GapWeightedFourierBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Long late mesh blocks recover Fourier coefficients uniformly. -/

import D5.S3.Analytic.Asymptotics.GapWeightedFourier

/-! Uniform Fourier recovery on long blocks of a mesh with vanishing gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace GapWeightedFourier

private theorem norm_block_phase (μ x : ℝ) : ‖phase μ x‖ = 1 := by
  rw [phase, mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal]

/-- Gap-weighted average on the left endpoints with indices in `[a,b)`. -/
def blockAverage (y : ℕ → ℝ) (f : ℕ → ℂ) (a b : ℕ) : ℂ :=
  (∑ k ∈ Finset.Ico a b, (gap y k : ℂ) * f k) / (↑(y b - y a) : ℂ)

private theorem sum_gap_Ico (y : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, gap y k) = y b - y a := by
  exact Finset.sum_Ico_sub (f := y) hab

private def phasePrimitive (μ x : ℝ) : ℂ := phase μ x / (Complex.I * (μ : ℂ))

private def phaseResidual (y : ℕ → ℝ) (μ : ℝ) (k : ℕ) : ℂ :=
  (gap y k : ℂ) * phase μ (y k) - (phasePrimitive μ (y (k + 1)) - phasePrimitive μ (y k))

private theorem norm_phaseResidual_le {y : ℕ → ℝ} (hm : StrictMono y)
    {μ : ℝ} (hμ : μ ≠ 0) (k : ℕ) :
    ‖phaseResidual y μ k‖ ≤ (‖μ‖ * gap y k) * gap y k := by
  let c : ℂ := Complex.I * (μ : ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hμ)
  have hcont : Continuous (phase μ) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul c)
  have hint (a b : ℝ) : (∫ t in a..b, phase μ t) = phasePrimitive μ b - phasePrimitive μ a := by
    simpa only [phasePrimitive, phase, c, sub_div] using
      (integral_exp_mul_complex (a := a) (b := b) hc)
  have hphase_sub (u t : ℝ) : ‖phase μ u - phase μ t‖ ≤ ‖μ‖ * ‖t - u‖ := by
    have hfactor : phase μ t - phase μ u =
        phase μ u * (Complex.exp (Complex.I * (↑(μ * (t - u)) : ℂ)) - 1) := by
      rw [mul_sub, mul_one]
      apply congrArg (fun z : ℂ => z - phase μ u)
      simp only [phase, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub]
      apply congrArg Complex.exp
      ring
    rw [norm_sub_rev, hfactor, norm_mul, norm_block_phase, one_mul, ← norm_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  have hle : y k ≤ y (k + 1) := (hm (Nat.lt_succ_self k)).le
  have heq : phaseResidual y μ k = ∫ t in y k..y (k + 1), phase μ (y k) - phase μ t := by
    rw [phaseResidual, intervalIntegral.integral_sub (intervalIntegrable_const (c := phase μ (y k)))
      (hcont.intervalIntegrable (y k) (y (k + 1))),
      intervalIntegral.integral_const, Complex.real_smul, hint, gap]
  have hpoint : ∀ t ∈ Set.uIoc (y k) (y (k + 1)),
      ‖phase μ (y k) - phase μ t‖ ≤ ‖μ‖ * gap y k := by
    intro t ht
    rw [Set.uIoc_of_le hle] at ht
    apply (hphase_sub (y k) t).trans
    rw [Real.norm_of_nonneg (sub_nonneg.mpr ht.1.le)]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 (y k)) (norm_nonneg μ)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  change _ ≤ (‖μ‖ * gap y k) * |gap y k| at hbound
  have hgap : 0 ≤ gap y k := sub_nonneg.mpr hle
  rw [abs_of_nonneg hgap] at hbound
  rw [heq]
  exact hbound

private theorem norm_phasePrimitive_sub_le (μ u v : ℝ) :
    ‖phasePrimitive μ v - phasePrimitive μ u‖ ≤ 2 / ‖μ‖ := by
  calc
    _ ≤ ‖phasePrimitive μ v‖ + ‖phasePrimitive μ u‖ := norm_sub_le _ _
    _ = _ := by
      simp only [phasePrimitive, norm_div, norm_block_phase, norm_mul, Complex.norm_I,
        Complex.norm_real, one_mul, ← add_div, one_add_one_eq_two]

/-- A single nonzero phase has a gap-weighted block average controlled by the
covered span and an upper bound on the gaps inside the block. -/
private theorem norm_blockAverage_phase_le {y : ℕ → ℝ} (hm : StrictMono y)
    {a b : ℕ} (hab : a < b) {μ δ : ℝ} (hμ : μ ≠ 0)
    (hgap : ∀ k ∈ Finset.Ico a b, gap y k ≤ δ) :
    ‖blockAverage y (fun k => phase μ (y k)) a b‖ ≤
      2 / (‖μ‖ * (y b - y a)) + ‖μ‖ * δ := by
  have hspan : 0 < y b - y a := sub_pos.mpr (hm hab)
  have hres : ‖∑ k ∈ Finset.Ico a b, phaseResidual y μ k‖ ≤
      (‖μ‖ * δ) * (y b - y a) := by
    rw [← sum_gap_Ico y hab.le, Finset.mul_sum]
    refine norm_sum_le_of_le _ fun k hk => ?_
    exact (norm_phaseResidual_le hm hμ k).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgap k hk) (norm_nonneg μ))
        (sub_nonneg.mpr (hm (Nat.lt_succ_self k)).le))
  have hsum : (∑ k ∈ Finset.Ico a b, (gap y k : ℂ) * phase μ (y k)) =
      (∑ k ∈ Finset.Ico a b, phaseResidual y μ k) +
        (phasePrimitive μ (y b) - phasePrimitive μ (y a)) := by
    simp only [phaseResidual, Finset.sum_sub_distrib,
      Finset.sum_Ico_sub (f := fun k => phasePrimitive μ (y k)) hab.le, sub_add_cancel]
  rw [blockAverage, norm_div, Complex.norm_of_nonneg hspan.le, hsum]
  calc
    _ ≤ (‖∑ k ∈ Finset.Ico a b, phaseResidual y μ k‖ +
          ‖phasePrimitive μ (y b) - phasePrimitive μ (y a)‖) / (y b - y a) :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hspan.le
    _ ≤ ((‖μ‖ * δ) * (y b - y a) + 2 / ‖μ‖) / (y b - y a) :=
      div_le_div_of_nonneg_right
        (add_le_add hres (norm_phasePrimitive_sub_le μ (y a) (y b))) hspan.le
    _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hspan.ne', div_div, add_comm]

private theorem tsum_mul_weighted_average {ι : Type*} {a : ι → ℂ}
    (ha : Summable (fun i => ‖a i‖)) {mode : ℕ → ι → ℂ}
    (hmode : ∀ k i, ‖mode k i‖ ≤ 1) (y : ℕ → ℝ) (s : Finset ℕ) (w : ℂ) :
    (∑' i, a i * ((∑ k ∈ s, (gap y k : ℂ) * mode k i) / w)) =
      (∑ k ∈ s, (gap y k : ℂ) * (∑' i, a i * mode k i)) / w := by
  let f : ℕ → ι → ℂ := fun k i => (gap y k : ℂ) * (a i * mode k i)
  have hf (k : ℕ) : Summable (f k) := by
    have hk : Summable (fun i => a i * mode k i) := ha.of_norm_bounded fun i => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hmode k i)
    exact hk.mul_left _
  calc
    _ = ∑' i, (∑ k ∈ s, f k i) / w := by
      apply tsum_congr
      intro i
      rw [← mul_div_assoc, Finset.mul_sum]
      apply congrArg (fun z : ℂ => z / w)
      refine Finset.sum_congr rfl fun k _ => ?_
      exact mul_left_comm _ _ _
    _ = (∑ k ∈ s, ∑' i, f k i) / w := by
      rw [tsum_div_const, Summable.tsum_finsetSum (fun k _ => hf k)]
    _ = _ := by simp only [f, tsum_mul_left]

private theorem phase_mul_neg (μ ν x : ℝ) :
    phase μ x * phase (-ν) x = phase (μ - ν) x := by
  simp only [phase, ← Complex.exp_add, Complex.ofReal_sub, Complex.ofReal_neg]
  apply congrArg Complex.exp
  ring

private theorem blockAverage_const {y : ℕ → ℝ} (hm : StrictMono y)
    {a b : ℕ} (hab : a < b) (z : ℂ) : blockAverage y (fun _ => z) a b = z := by
  have hd : (↑(y b - y a) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hm hab).ne')
  rw [blockAverage, ← Finset.sum_mul, ← Complex.ofReal_sum, sum_gap_Ico y hab.le, mul_comm]
  exact mul_div_cancel_right₀ z hd

private theorem norm_blockAverage_le {y : ℕ → ℝ} (hm : StrictMono y)
    {a b : ℕ} (hab : a < b) {f : ℕ → ℂ} {M : ℝ}
    (h : ∀ k ∈ Finset.Ico a b, ‖f k‖ ≤ M) :
    ‖blockAverage y f a b‖ ≤ M := by
  have hspan : 0 < y b - y a := sub_pos.mpr (hm hab)
  rw [blockAverage, norm_div, Complex.norm_of_nonneg hspan.le, div_le_iff₀ hspan,
    ← sum_gap_Ico y hab.le, Finset.mul_sum]
  refine norm_sum_le_of_le _ fun k hk => ?_
  have hgap : 0 ≤ gap y k := sub_nonneg.mpr (hm (Nat.lt_succ_self k)).le
  rw [norm_mul, Complex.norm_of_nonneg hgap, mul_comm M]
  exact mul_le_mul_of_nonneg_left (h k hk) (sub_nonneg.mpr (hm (Nat.lt_succ_self k)).le)

/-- A finite set of modes controls the block recovery error up to the absolute
coefficient mass outside that set. Modes at the target frequency contribute
exactly their coefficients, including outside the finite set. -/
private theorem norm_blockAverage_modulated_series_sub_le {ι : Type*} {y : ℕ → ℝ}
    (hm : StrictMono y) {a b : ℕ} (hab : a < b) {δ : ℝ}
    (hgap : ∀ k ∈ Finset.Ico a b, gap y k ≤ δ)
    (c : ι → ℂ) (freq : ι → ℝ) (hc : Summable (fun i => ‖c i‖)) (ν : ℝ)
    (E : Finset ι) :
    ‖blockAverage y
          (fun k => (∑' i, c i * phase (freq i) (y k)) * phase (-ν) (y k)) a b -
        (∑' i, if freq i = ν then c i else 0)‖ ≤
      (∑ i ∈ E, if freq i = ν then 0 else
        ‖c i‖ * (2 / (‖freq i - ν‖ * (y b - y a)) + ‖freq i - ν‖ * δ)) +
      (∑' i : {i // i ∉ E}, ‖c i‖) := by
  let mode : ℕ → ι → ℂ := fun k i => phase (freq i - ν) (y k)
  let term : ι → ℂ := fun i => c i * blockAverage y (fun k => mode k i) a b
  let coeff : ι → ℂ := fun i => if freq i = ν then c i else 0
  let d : ι → ℂ := fun i => term i - coeff i
  have hmode (k : ℕ) (i : ι) : ‖mode k i‖ ≤ 1 := (norm_block_phase _ _).le
  have hterm (i : ι) : ‖term i‖ ≤ ‖c i‖ := by
    dsimp only [term]
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_blockAverage_le hm hab fun k _ => hmode k i)
  have hzero (i : ι) (hi : freq i = ν) : d i = 0 := by
    have hz : (fun k => mode k i) = fun _ => (1 : ℂ) := by
      simp only [mode, hi, sub_self, phase, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero]
    simp only [d, term, coeff, ite_eq_left hi, hz, blockAverage_const hm hab, mul_one, sub_self]
  have hnonzero (i : ι) (hi : freq i ≠ ν) : d i = term i := by
    simp only [d, coeff, ite_eq_right hi, sub_zero]
  have hdom (i : ι) : ‖d i‖ ≤ ‖c i‖ := by
    by_cases hi : freq i = ν
    · simpa only [hzero i hi, norm_zero] using norm_nonneg (c i)
    · simpa only [hnonzero i hi] using hterm i
  have hd : Summable (fun i => ‖d i‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hdom hc
  have hcoeff : Summable coeff := hc.of_norm_bounded fun i => by
    by_cases hi : freq i = ν <;> simp [coeff, hi]
  have hexchange :
      (∑' i, term i) = blockAverage y (fun k => ∑' i, c i * mode k i) a b :=
    tsum_mul_weighted_average hc hmode y (Finset.Ico a b) (↑(y b - y a) : ℂ)
  have htwist :
      (fun k => (∑' i, c i * phase (freq i) (y k)) * phase (-ν) (y k)) =
        fun k => ∑' i, c i * mode k i := by
    funext k
    rw [← tsum_mul_right]
    apply tsum_congr
    intro i
    simp only [mul_assoc, phase_mul_neg, mode]
  have hdiff :
      (∑' i, term i) - (∑' i, coeff i) = ∑' i, d i :=
    ((hc.of_norm_bounded hterm).tsum_sub hcoeff).symm
  have hfinite : ‖∑ i ∈ E, d i‖ ≤
      ∑ i ∈ E, if freq i = ν then 0 else
        ‖c i‖ * (2 / (‖freq i - ν‖ * (y b - y a)) + ‖freq i - ν‖ * δ) := by
    refine norm_sum_le_of_le _ fun i _ => ?_
    by_cases hi : freq i = ν
    · simpa only [hzero i hi, ite_eq_left hi, norm_zero] using (le_rfl : (0 : ℝ) ≤ 0)
    · rw [hnonzero i hi, ite_eq_right hi]
      dsimp only [term]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_blockAverage_phase_le hm hab (sub_ne_zero.mpr hi) hgap) (norm_nonneg _)
  have htail : ‖∑' i : {i // i ∉ E}, d i‖ ≤ ∑' i : {i // i ∉ E}, ‖c i‖ := by
    exact tsum_of_norm_bounded (hc.subtype {i | i ∉ E}).hasSum (fun i => hdom i)
  rw [htwist, ← hexchange]
  change ‖(∑' i, term i) - (∑' i, coeff i)‖ ≤ _
  rw [hdiff, ← hd.of_norm.sum_add_tsum_subtype_compl E]
  exact (norm_add_le _ _).trans (add_le_add hfinite htail)

/-- Every sufficiently late mesh block of sufficiently large span recovers the
coefficient at the chosen frequency to prescribed precision, even when the
samples have a perturbation tending to zero. -/
theorem eventually_blockAverage_modulated_series {ι : Type*} {y : ℕ → ℝ}
    (hm : StrictMono y) (hgap : Tendsto (gap y) atTop (𝓝 0))
    (c : ι → ℂ) (freq : ι → ℝ) (hc : Summable (fun i => ‖c i‖))
    (ν : ℝ) (s : ℕ → ℂ)
    (hs : Tendsto (fun k => s k - ∑' i, c i * phase (freq i) (y k)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, ∃ H : ℝ, 0 < H ∧ ∀ ⦃a b : ℕ⦄, A ≤ a → a < b → H ≤ y b - y a →
      ‖blockAverage y (fun k => s k * phase (-ν) (y k)) a b -
        (∑' i, if freq i = ν then c i else 0)‖ ≤ ε := by
  classical
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨E, hE⟩ := eventually_atTop.1
    ((tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖)).eventually (gt_mem_nhds hε3))
  let K : ℝ := ∑ i ∈ E, if freq i = ν then 0 else ‖c i‖ * (2 / ‖freq i - ν‖ + ‖freq i - ν‖)
  have hK : 0 ≤ K := by
    dsimp [K]
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs <;> positivity
  let δ : ℝ := (ε / 3) / (K + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKδ : K * δ ≤ ε / 3 := by
    calc
      K * δ ≤ (K + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 3 := by
        dsimp only [δ]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : K + 1 ≠ 0)]
  have her : ∀ᶠ k in atTop, ‖s k - ∑' i, c i * phase (freq i) (y k)‖ < ε / 3 :=
    (tendsto_zero_iff_norm_tendsto_zero.mp hs).eventually (gt_mem_nhds hε3)
  obtain ⟨A, hA⟩ := eventually_atTop.1 (her.and (hgap.eventually (gt_mem_nhds hδ)))
  refine ⟨A, δ⁻¹, inv_pos.mpr hδ, fun a b ha hab hspan => ?_⟩
  let S : ℕ → ℂ := fun k => ∑' i, c i * phase (freq i) (y k)
  have hinv : (y b - y a)⁻¹ ≤ δ := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hδ) hspan
  have hfinite :
      (∑ i ∈ E, if freq i = ν then 0 else
        ‖c i‖ * (2 / (‖freq i - ν‖ * (y b - y a)) + ‖freq i - ν‖ * δ)) ≤ K * δ := by
    dsimp only [K]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : freq i = ν
    · simp [hi]
    · rw [ite_eq_right hi, ite_eq_right hi, mul_assoc, add_mul, ← div_div]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg (c i))
      apply add_le_add_left
      rw [div_eq_mul_inv (2 / ‖freq i - ν‖)]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hpure : ‖blockAverage y (fun k => S k * phase (-ν) (y k)) a b -
      (∑' i, if freq i = ν then c i else 0)‖ ≤ ε / 3 + ε / 3 := by
    refine (norm_blockAverage_modulated_series_sub_le hm hab (δ := δ) ?_ c freq hc ν E).trans ?_
    · intro k hk
      exact (hA k (ha.trans (Finset.mem_Ico.mp hk).1)).2.le
    · exact add_le_add (hfinite.trans hKδ) (hE E le_rfl).le
  have herr : ‖blockAverage y (fun k => (s k - S k) * phase (-ν) (y k)) a b‖ ≤ ε / 3 := by
    apply norm_blockAverage_le hm hab
    intro k hk
    rw [norm_mul, norm_block_phase, mul_one]
    exact (hA k (ha.trans (Finset.mem_Ico.mp hk).1)).1.le
  have hdiff : blockAverage y (fun k => s k * phase (-ν) (y k)) a b -
      blockAverage y (fun k => S k * phase (-ν) (y k)) a b =
      blockAverage y (fun k => (s k - S k) * phase (-ν) (y k)) a b := by
    simp only [blockAverage, ← sub_div, ← Finset.sum_sub_distrib, sub_mul, mul_sub]
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (blockAverage y (fun k => s k * phase (-ν) (y k)) a b)
    (blockAverage y (fun k => S k * phase (-ν) (y k)) a b)
    (∑' i, if freq i = ν then c i else 0)
  rw [hdiff] at htriangle
  linarith only [htriangle, hpure, herr]

end GapWeightedFourier
