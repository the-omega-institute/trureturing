/- GID: D5/S3/StatisticalMechanics/DelayedCooling/Kernel
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DelayedCooling/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete delayed relaxation and its differential equation. -/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.Monotone.Union
public import Mathlib.Tactic

/-!
# The quasi-exponential relaxation

The extension to negative times is the constant equilibrium history. The
cutoff-power representation agrees with the finite sum in Santos, Eq. (6),
and permits local finite-sum calculations at the step boundaries.
-/

public section

namespace D5.S3.StatisticalMechanics.DelayedCooling.Kernel

open Set Filter
open scoped Topology BigOperators

noncomputable section

private def cutPower (n : ℕ) (x : ℝ) : ℝ := min x 0 ^ (n + 1)

private theorem continuous_cutPower (n : ℕ) : Continuous (cutPower n) := by
  exact (continuous_id.min continuous_const).pow _

private theorem hasDerivAt_cutPower_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (cutPower (n + 1)) ((n + 2 : ℕ) * min x 0 ^ (n + 1)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_id x).fun_pow (n + 2)
    convert h.congr_of_eventuallyEq ?_ using 1
    · simp [min_eq_left hx.le, show n + 2 - 1 = n + 1 by omega]
    · filter_upwards [Iio_mem_nhds hx] with y hy
      simp [cutPower, min_eq_left (le_of_lt (mem_Iio.mp hy)), Nat.add_assoc]
  · have hl : HasDerivWithinAt (cutPower (n + 1)) 0 (Iic 0) 0 := by
      have hp : HasDerivAt (fun x : ℝ => x ^ (n + 2)) 0 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).fun_pow (n + 2)
      exact hp.hasDerivWithinAt.congr
        (fun y hy => by simp [cutPower, min_eq_left (mem_Iic.mp hy), Nat.add_assoc])
        (by simp [cutPower])
    have hr : HasDerivWithinAt (cutPower (n + 1)) 0 (Ici 0) 0 := by
      exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun y hy => by simp [cutPower, min_eq_right (mem_Ici.mp hy), Nat.add_assoc])
        (by simp [cutPower])
    simpa [Iic_union_Ici] using hl.union hr
  · have h := hasDerivAt_const x (0 : ℝ)
    convert h.congr_of_eventuallyEq ?_ using 1
    · simp [min_eq_right hx.le]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [cutPower, min_eq_right (le_of_lt (mem_Ioi.mp hy))]

/-- A cutoff summand in the source finite sum. -/
private def term (τ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  cutPower n ((n : ℝ) * τ - t) / (n + 1).factorial

private def stepSum (τ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  1 + ∑ n ∈ Finset.range N, term τ n t

/-- The source quasi-exponential, including its constant negative-time history. -/
def relaxation (τ t : ℝ) : ℝ := stepSum τ (⌊t / τ⌋₊ + 1) t

private theorem term_eq_zero {τ t : ℝ} {n : ℕ} (h : t ≤ (n : ℝ) * τ) :
    term τ n t = 0 := by
  simp [term, cutPower, min_eq_right (sub_nonneg.mpr h)]

private theorem stepSum_stable {τ t : ℝ} (hτ : 0 < τ) {N M : ℕ}
    (hNM : N ≤ M) (ht : t ≤ (N : ℝ) * τ) : stepSum τ M t = stepSum τ N t := by
  unfold stepSum
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n hn hnN
  apply term_eq_zero
  have hNn : N ≤ n := by simpa using hnN
  exact ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hNn) hτ.le)

private theorem relaxation_eq_stepSum {τ t : ℝ} (hτ : 0 < τ) {N : ℕ}
    (ht : t ≤ (N : ℝ) * τ) : relaxation τ t = stepSum τ N t := by
  have hf : t ≤ ((⌊t / τ⌋₊ + 1 : ℕ) : ℝ) * τ := by
    have := Nat.lt_floor_add_one (t / τ)
    exact ((div_lt_iff₀ hτ).mp (by simpa using this)).le
  unfold relaxation
  rcases le_total N (⌊t / τ⌋₊ + 1) with h | h
  · exact stepSum_stable hτ h ht
  · exact (stepSum_stable hτ h hf).symm

private theorem relaxation_eventually_stepSum {τ t : ℝ} (hτ : 0 < τ) {N : ℕ}
    (ht : t < (N : ℝ) * τ) : relaxation τ =ᶠ[𝓝 t] stepSum τ N := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact relaxation_eq_stepSum hτ hs.le

/-- The literal finite sum of source Eq. (6), for every nonnegative real time. -/
theorem relaxation_eq_source_sum {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    relaxation τ t =
      1 + ∑ n ∈ Finset.range (⌊t / τ⌋₊ + 1),
        (((n : ℝ) * τ - t) ^ (n + 1)) / (n + 1).factorial := by
  unfold relaxation stepSum
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ ⌊t / τ⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hnt : (n : ℝ) * τ ≤ t := by
    exact (le_div_iff₀ hτ).mp ((Nat.cast_le.mpr hn').trans (Nat.floor_le (div_nonneg ht hτ.le)))
  simp [term, cutPower, min_eq_left (sub_nonpos.mpr hnt)]

/-- Negative times retain the equilibrated value, including the value at zero. -/
theorem relaxation_of_nonpos {τ t : ℝ} (hτ : 0 < τ) (ht : t ≤ 0) :
    relaxation τ t = 1 := by
  rw [relaxation_eq_stepSum hτ (N := 0) (by simpa using ht)]
  simp [stepSum]

/-- The first polynomial segment includes both endpoints. -/
theorem relaxation_initial_segment {τ t : ℝ} (hτ : 0 < τ)
    (ht : 0 ≤ t) (htτ : t ≤ τ) : relaxation τ t = 1 - t := by
  rw [relaxation_eq_source_sum hτ ht]
  rcases lt_or_eq_of_le htτ with hlt | rfl
  · have hf : ⌊t / τ⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hτ).mpr hlt)
    simp [hf, sub_eq_add_neg]
  · simp [hτ.ne', Finset.sum_range_succ, sub_eq_add_neg]

private theorem continuous_stepSum (τ : ℝ) (N : ℕ) : Continuous (stepSum τ N) := by
  unfold stepSum term
  exact continuous_const.add (continuous_finsetSum _ (fun n _ =>
    ((continuous_cutPower n).comp (continuous_const.sub continuous_id)).div_const _))

/-- All step boundaries glue continuously, including the equilibrium endpoint. -/
theorem continuous_relaxation {τ : ℝ} (hτ : 0 < τ) : Continuous (relaxation τ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : t < ((⌊t / τ⌋₊ + 1 : ℕ) : ℝ) * τ := by
    exact (div_lt_iff₀ hτ).mp (by simpa using Nat.lt_floor_add_one (t / τ))
  exact (continuous_stepSum τ _).continuousAt.congr
    (relaxation_eventually_stepSum hτ ht).symm

private theorem hasDerivAt_term_zero (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (term τ 0) (-1) t := by
  apply (hasDerivAt_neg t).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp [term, cutPower, min_eq_left (neg_nonpos.mpr (mem_Ioi.mp hs).le)]

private theorem hasDerivAt_term_succ (τ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (term τ (n + 1)) (-term τ n (t - τ)) t := by
  have h := ((hasDerivAt_cutPower_succ n (((n + 1 : ℕ) : ℝ) * τ - t)).comp t
    ((hasDerivAt_const t (((n + 1 : ℕ) : ℝ) * τ)).sub (hasDerivAt_id t))).div_const
      (((n + 2).factorial : ℕ) : ℝ)
  change HasDerivAt (term τ (n + 1)) _ t at h
  convert h using 1
  unfold term cutPower
  have he : ((n + 1 : ℕ) : ℝ) * τ - t = (n : ℝ) * τ - (t - τ) := by
    push_cast
    ring
  rw [he, Nat.factorial_succ (n + 1)]
  push_cast
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem hasDerivAt_stepSum (τ : ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (stepSum τ (N + 1)) (-stepSum τ N (t - τ)) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_term_succ τ n t)
  have h := (hasDerivAt_const t (1 : ℝ)).add
    (hsum.add (hasDerivAt_term_zero τ ht))
  convert h using 1
  · ext s
    simp [stepSum, Finset.sum_range_succ']
  · simp [stepSum, ← Finset.sum_neg_distrib]

/-- The delayed differential equation holds at every strictly positive real time,
including all positive step boundaries. No differentiability at zero is asserted. -/
theorem hasDerivAt_relaxation {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) :
    HasDerivAt (relaxation τ) (-relaxation τ (t - τ)) t := by
  let N := ⌊t / τ⌋₊ + 1
  have hN : t < (N : ℝ) * τ :=
    (div_lt_iff₀ hτ).mp (by simpa [N] using Nat.lt_floor_add_one (t / τ))
  have hNp : t < ((N + 1 : ℕ) : ℝ) * τ := by
    push_cast
    linarith
  have hshift : t - τ ≤ (N : ℝ) * τ := by linarith
  rw [relaxation_eq_stepSum hτ hshift]
  exact (hasDerivAt_stepSum τ N ht).congr_of_eventuallyEq
    (relaxation_eventually_stepSum hτ hNp)

private def weighted (τ κ t : ℝ) : ℝ := Real.exp (κ * t) * relaxation τ t

private def weightedRate (τ κ t : ℝ) : ℝ :=
  Real.exp (κ * t) * (κ * relaxation τ t - relaxation τ (t - τ))

private theorem continuous_weighted {τ : ℝ} (hτ : 0 < τ) (κ : ℝ) :
    Continuous (weighted τ κ) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_relaxation hτ)

private theorem continuous_weightedRate {τ : ℝ} (hτ : 0 < τ) (κ : ℝ) :
    Continuous (weightedRate τ κ) := by
  unfold weightedRate
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((continuous_const.mul (continuous_relaxation hτ)).sub
      ((continuous_relaxation hτ).comp (continuous_id.sub continuous_const)))

private theorem hasDerivAt_weighted {τ t : ℝ} (hτ : 0 < τ) (κ : ℝ) (ht : 0 < t) :
    HasDerivAt (weighted τ κ) (weightedRate τ κ t) t := by
  convert (((hasDerivAt_id t).const_mul κ).exp).mul (hasDerivAt_relaxation hτ ht) using 1
  · rfl
  · dsimp [weightedRate]
    ring

private theorem weightedRate_pos {τ κ : ℝ} (hτ : 0 < τ) (hκ : 1 < κ)
    (hroot : Real.exp (κ * τ) ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    0 < weightedRate τ κ t := by
  have hzero : 0 < weightedRate τ κ 0 := by
    have hn : relaxation τ (-τ) = 1 := relaxation_of_nonpos hτ (by linarith)
    simpa [weightedRate, relaxation_of_nonpos hτ (le_refl 0), hn] using sub_pos.mpr hκ
  by_contra hbad
  let S : Set ℝ := Icc 0 t ∩ {s | weightedRate τ κ s ≤ 0}
  have hc : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le (continuous_weightedRate hτ κ) continuous_const)
  obtain ⟨T, hT⟩ := hc.exists_isLeast ⟨t, ⟨⟨ht, le_rfl⟩, le_of_not_gt hbad⟩⟩
  have hT0 : 0 < T := by
    have hTn := hT.1.1.1
    have hTbad := hT.1.2
    have hne : T ≠ 0 := by intro he; subst T; exact (not_le_of_gt hzero) hTbad
    exact lt_of_le_of_ne hTn (Ne.symm hne)
  have hpre : ∀ s ∈ Ioo 0 T, 0 < weightedRate τ κ s := by
    intro s hs
    by_contra hh
    have hmem : s ∈ S := ⟨⟨hs.1.le, hs.2.le.trans hT.1.1.2⟩, le_of_not_gt hh⟩
    exact (not_le_of_gt hs.2) (hT.2 hmem)
  have hm : StrictMonoOn (weighted τ κ) (Icc 0 T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_weighted hτ κ).continuousOn
    intro s hs
    rw [interior_Icc] at hs
    rw [(hasDerivAt_weighted hτ κ hs.1).deriv]
    exact hpre s hs
  have hneg : StrictMonoOn (weighted τ κ) (Iic 0) := by
    intro x hx y hy hxy
    simp only [weighted, relaxation_of_nonpos hτ hx, relaxation_of_nonpos hτ hy, mul_one]
    exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxy (lt_trans zero_lt_one hκ))
  have hall : StrictMonoOn (weighted τ κ) (Iic 0 ∪ Icc 0 T) :=
    hneg.union hm isGreatest_Iic (isLeast_Icc hT0.le)
  have hTm : T - τ ∈ Iic 0 ∪ Icc 0 T := by
    by_cases hh : T - τ ≤ 0
    · exact Or.inl hh
    · exact Or.inr ⟨le_of_not_ge hh, by linarith⟩
  have hTmem : T ∈ Iic 0 ∪ Icc 0 T := Or.inr ⟨hT0.le, le_rfl⟩
  have hinc : weighted τ κ (T - τ) < weighted τ κ T :=
    hall hTm hTmem (by linarith)
  have hpast : 0 < weighted τ κ (T - τ) := by
    by_cases hh : T - τ ≤ 0
    · simp [weighted, relaxation_of_nonpos hτ hh, Real.exp_pos]
    · have hh0 : 0 < T - τ := lt_of_not_ge hh
      have h := hm ⟨le_rfl, hT0.le⟩ ⟨hh0.le, by linarith⟩ hh0
      have hz : weighted τ κ 0 = 1 := by simp [weighted, relaxation_of_nonpos hτ (le_refl 0)]
      rw [hz] at h
      linarith
  have hrate : weightedRate τ κ T =
      κ * weighted τ κ T - Real.exp (κ * τ) * weighted τ κ (T - τ) := by
    unfold weightedRate weighted
    rw [← mul_assoc (Real.exp (κ * τ)), ← Real.exp_add]
    have he : κ * τ + κ * (T - τ) = κ * T := by ring
    rw [he]
    ring
  have hpos : 0 < weightedRate τ κ T := by
    rw [hrate]
    nlinarith [mul_pos (lt_trans zero_lt_one hκ) (sub_pos.mpr hinc),
      mul_nonneg (sub_nonneg.mpr hroot) hpast.le]
  exact (not_le_of_gt hpos) hT.1.2

/-- The actual source relaxation remains strictly positive for every real time
throughout the nonoscillatory delay range, including its critical endpoint. -/
theorem relaxation_pos {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1)) (t : ℝ) :
    0 < relaxation τ t := by
  by_cases ht : t ≤ 0
  · rw [relaxation_of_nonpos hτ ht]
    exact zero_lt_one
  · have ht0 : 0 < t := lt_of_not_ge ht
    let κ := Real.exp 1
    have hκ : 1 < κ := Real.one_lt_exp_iff.mpr (by norm_num)
    have hprod : κ * τ ≤ 1 := by
      calc
        κ * τ ≤ Real.exp 1 * Real.exp (-1) := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; norm_num
    have hroot : Real.exp (κ * τ) ≤ κ := Real.exp_le_exp.mpr hprod
    have hm : StrictMonoOn (weighted τ κ) (Icc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_weighted hτ κ).continuousOn
      intro s hs
      rw [interior_Icc] at hs
      rw [(hasDerivAt_weighted hτ κ hs.1).deriv]
      exact weightedRate_pos hτ hκ hroot s hs.1.le
    have hh := hm ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩ ht0
    have hz : weighted τ κ 0 = 1 := by simp [weighted, relaxation_of_nonpos hτ (le_refl 0)]
    rw [hz] at hh
    have hpos : 0 < weighted τ κ t := lt_trans zero_lt_one hh
    exact (mul_pos_iff_of_pos_left (Real.exp_pos (κ * t))).mp hpos

/-- Strict cooling of the single-quench response on the entire nonnegative half-line. -/
theorem strictAntiOn_relaxation {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1)) :
    StrictAntiOn (relaxation τ) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_relaxation hτ).continuousOn
  intro t ht
  rw [interior_Ici] at ht
  rw [(hasDerivAt_relaxation hτ ht).deriv]
  exact neg_neg_of_pos (relaxation_pos hτ hsmall _)

/-- The equilibrium extension is nonincreasing on the whole real line. -/
theorem antitone_relaxation {τ : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) : Antitone (relaxation τ) := by
  intro x y hxy
  by_cases hy : y ≤ 0
  · simp [relaxation_of_nonpos hτ hy, relaxation_of_nonpos hτ (hxy.trans hy)]
  by_cases hx : x ≤ 0
  · rw [relaxation_of_nonpos hτ hx]
    have hh := (strictAntiOn_relaxation hτ hsmall).antitoneOn
      (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show y ∈ Ici 0 from le_of_not_ge hy)
      (le_of_not_ge hy)
    simpa [relaxation_of_nonpos hτ (le_refl 0)] using hh
  · exact (strictAntiOn_relaxation hτ hsmall).antitoneOn
      (le_of_not_ge hx) (le_of_not_ge hy) hxy

/-- A uniform exponential upper bound; the delay response decays at least as fast
as the memoryless exponential in this parameter range. -/
theorem relaxation_le_exp_neg {τ t : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1))
    (ht : 0 ≤ t) : relaxation τ t ≤ Real.exp (-t) := by
  have hd : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s => Real.exp s * relaxation τ s)
        (Real.exp s * (relaxation τ s - relaxation τ (s - τ))) s := by
    intro s hs
    convert (Real.hasDerivAt_exp s).mul (hasDerivAt_relaxation hτ hs) using 1
    ring
  have hm : AntitoneOn (fun s => Real.exp s * relaxation τ s) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      (Real.continuous_exp.mul (continuous_relaxation hτ)).continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (hd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change deriv (fun s => Real.exp s * relaxation τ s) s ≤ 0
      rw [(hd s hs).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (antitone_relaxation hτ hsmall (by linarith : s - τ ≤ s)))
  have hb := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) ht ht
  simp only [Real.exp_zero, relaxation_of_nonpos hτ (le_refl 0), mul_one] at hb
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

/-- The concrete relaxation tends to the target equilibrium. -/
theorem tendsto_relaxation_atTop {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1)) :
    Tendsto (relaxation τ) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun t => (relaxation_pos hτ hsmall t).le))
    _ Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact relaxation_le_exp_neg hτ hsmall ht

end

end D5.S3.StatisticalMechanics.DelayedCooling.Kernel
