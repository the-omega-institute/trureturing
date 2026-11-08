/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentFreezing
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentFreezing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth energy yields uniform moving moments and fourth-order cell freezing estimates. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentEndpoint
import D5.S3.Arith.Robin.ForwardKernel.MacroscopicFreezing

/-! Uniform fourth moments and freezing estimates for macroscopic lengths. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentFreezing

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs FourthMomentTransferDefs MacroscopicVarianceDefs
open MovingLengthCells MacroscopicEndpointGeometry DyadicProbability MomentTransferDefs

noncomputable section
set_option autoImplicit false

/-- Fourth energy controls comparison with a fixed length on any macroscopic subinterval. -/
theorem macro_fourth_comparison
    {E a : ℝ → ℝ} {α θ β C M L X ε l r c R : ℝ}
    (hE : LocallyBoundedMeasurable E) (_hB : ValidBand α θ β)
    (ha : MacroscopicLengthBounds a M L) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hX : 4 ≤ X) (hε : 0 ≤ ε) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * X)
    (hc : c ∈ Icc (0 : ℝ) M) (hR : 0 < R)
    (hV : localFourthEnergyWindow E α β C X ε)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2)
    (hlo : (4 * X) ^ α ≤ R) (hhi : 4 * R ≤ (X / 2) ^ β)
    (hgap : ∀ x ∈ Icc l r, |X ^ θ * (a (x / X) - c)| ≤ R) :
    (∫ x in l..r, |macroIncrement E a θ X x - increment E (X ^ θ * c) x| ^ 4) ≤
      (1312 / 3 : ℝ) * C * R ^ 2 * Real.log X ^ 2 *
        (r + M * X ^ θ - l + ε * X) := by
  have hX0 : 0 < X := by linarith
  have hH := Real.rpow_pos_of_pos hX0 θ
  obtain ⟨q', hp, hq, hdp, hdq, hdq_lower, himage⟩ :=
    macro_endpoint_geometry ha hM hX0 hl hlr hr hc hMX hLX
  have hh := FourthMomentEndpoint.local_fourth_endpoint_bound hE hC hε hX hlr
    (show l ≤ r + M * X ^ θ by nlinarith [mul_nonneg hM hH.le]) hR
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) (by linarith) hlo hhi hV
    hp hq hdp hdq (fun x hx => ⟨by norm_num, hdq_lower x hx⟩) himage (by
      intro x hx
      convert hgap x hx using 1
      congr 1
      ring)
  convert hh using 1
  · apply intervalIntegral.integral_congr
    intro x _
    congr 2
    dsimp [macroIncrement, increment]
    ring
  · ring

private lemma probability_fourth_le {X : ℝ} (hX : 0 < X) {f : ℝ → ℝ}
    (hi : IntervalIntegrable (fun x => |f x| ^ 4) volume X (2 * X)) :
    (∫ x, |f x| ^ 4 ∂dyadicProbabilityMeasure X) ≤
      (∫ x in X..(2 * X), |f x| ^ 4) / (X * Real.log 2) := by
  have hXX : X ≤ 2 * X := by linarith
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc X (2 * X)) := by
    apply continuousOn_id.inv₀
    intro x hx
    rw [uIcc_of_le hXX] at hx
    exact (hX.trans_le hx.1).ne'
  have hiw := hi.mul_continuousOn hc
  rw [dyadicProbabilityMeasure_integral hX]
  calc
    _ ≤ (∫ x in X..(2 * X), |f x| ^ 4 / X) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
      apply intervalIntegral.integral_mono_on hXX
        (by simpa only [div_eq_mul_inv] using hiw) (hi.div_const X)
      intro x hx
      exact div_le_div_of_nonneg_left (by positivity) hX hx.1
    _ = _ := by rw [intervalIntegral.integral_div]; ring

private lemma macro_fourth_integrable {E a : ℝ → ℝ} {θ X c : ℝ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X)
    (ha : ContinuousOn a (Icc (1 : ℝ) 2)) :
    IntervalIntegrable (fun x => |macroIncrement E a θ X x - increment E c x| ^ 4)
      volume X (2 * X) := by
  let ae := IccExtend (by norm_num : (1 : ℝ) ≤ 2) (fun u : Icc (1 : ℝ) 2 => a u)
  have hae : Continuous ae := ha.domRestrict.Icc_extend'
  have hu : Continuous (fun x : ℝ => x + X ^ θ * ae (x / X)) := by fun_prop
  have hp : Continuous (fun x : ℝ => x + c) := by fun_prop
  have hi := VarianceTransfer.increment_pow_integrableOn (μ := volume) (K := uIcc X (2 * X)) hE isCompact_uIcc
    (hu.sub hp) hp 4
  apply hi.intervalIntegrable.congr
  intro x hx
  rw [uIoc_of_le (by linarith : X ≤ 2 * X)] at hx
  have hx' : x / X ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hX).2 (by linarith [hx.1]), (div_le_iff₀ hX).2 hx.2⟩
  change (E ((x + c) + ((x + X ^ θ * ae (x / X)) - (x + c))) - E (x + c)) ^ 4 =
    |(E (x + X ^ θ * a (x / X)) - E x) - (E (x + c) - E x)| ^ 4
  have hae' : ae (x / X) = a (x / X) := IccExtend_of_mem _ _ hx'
  rw [hae', show (x + c) + ((x + X ^ θ * a (x / X)) - (x + c)) =
    x + X ^ θ * a (x / X) by ring, Even.pow_abs (by decide : Even 4)]
  congr 1
  ring

private lemma normalized_comparison_integral {E a : ℝ → ℝ} {θ X c : ℝ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X)
    (ha : ContinuousOn a (Icc (1 : ℝ) 2)) :
    IntervalIntegrable (fun x => |movingB E a θ X x - fixedScaleB E θ c X x| ^ 4)
      volume X (2 * X) := by
  have hi := (macro_fourth_integrable (θ := θ) (c := X ^ θ * c) hE hX ha).div_const
    (Real.sqrt (X ^ θ * Real.log X) ^ 4)
  apply hi.congr
  intro x _
  simp only [movingB, fixedScaleB, dyadicU, macroIncrement, ← sub_div, abs_div, div_pow,
    mul_comm c (X ^ θ), mul_comm (a (x / X)) (X ^ θ), abs_pow, Even.pow_abs (by decide : Even 4)]

private lemma frozenB_on_cell {E a : ℝ → ℝ} {θ X x : ℝ} {n j : ℕ}
    (_hn : 0 < n) (hj : j < n) (hX : 0 < X)
    (hx : x ∈ Ioc (cellPoint n j * X) (cellPoint n (j + 1) * X)) :
    frozenB E a θ n X x = fixedScaleB E θ (a (cellPoint n j)) X x := by
  have hu : dyadicU X x ∈ Ioc (cellPoint n j) (cellPoint n (j + 1)) :=
    ⟨(lt_div_iff₀ hX).2 hx.1, (div_le_iff₀ hX).2 hx.2⟩
  exact cell_step_eval (Finset.mem_range.mpr hj) hu
    (fun l => fixedScaleB E θ (a (cellPoint n l)) X x)

private lemma cell_subset {X : ℝ} {n j : ℕ} (hX : 0 < X) (hn : 0 < n) (hj : j < n) :
    uIcc (cellPoint n j * X) (cellPoint n (j + 1) * X) ⊆ uIcc X (2 * X) := by
  rw [uIcc_of_le (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX.le),
    uIcc_of_le (by linarith : X ≤ 2 * X)]
  exact Icc_subset_Icc
    (by nlinarith [(cellPoint_mem hn hj.le).1])
    (by nlinarith [(cellPoint_mem hn (Nat.succ_le_of_lt hj)).2])

private lemma probability_cell_sum_le {X T : ℝ} {n : ℕ} {f : ℝ → ℝ}
    (hX : 0 < X) (hn : 0 < n)
    (hi : ∀ j < n, IntervalIntegrable (fun x => |f x| ^ 4) volume
      (cellPoint n j * X) (cellPoint n (j + 1) * X))
    (hb : ∀ j < n, (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
      |f x| ^ 4) ≤ T) :
    (∫ x, |f x| ^ 4 ∂dyadicProbabilityMeasure X) ≤ (n : ℝ) * T / (X * Real.log 2) := by
  have his := IntervalIntegrable.trans_iterate hi
  have hs := intervalIntegral.sum_integral_adjacent_intervals hi
  norm_num [cellPoint, hn.ne'] at his hs
  apply (probability_fourth_le hX his).trans
  apply div_le_div_of_nonneg_right _ (by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
  rw [← hs]
  simpa [cellPoint] using Finset.sum_le_sum (s := Finset.range n) (g := fun _ => T)
    (fun j hj => hb j (Finset.mem_range.1 hj))

private lemma normalized_cell_comparison
    {E a : ℝ → ℝ} {α θ β C M L X ε l r c R : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (ha : MacroscopicLengthBounds a M L) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hX : 4 ≤ X) (hε : 0 ≤ ε) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * X)
    (hc : c ∈ Icc (0 : ℝ) M) (hR : 0 < R)
    (hV : localFourthEnergyWindow E α β C X ε)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2)
    (hlo : (4 * X) ^ α ≤ R) (hhi : 4 * R ≤ (X / 2) ^ β)
    (hgap : ∀ x ∈ Icc l r, |X ^ θ * (a (x / X) - c)| ≤ R) :
    (∫ x in l..r, |movingB E a θ X x - fixedScaleB E θ c X x| ^ 4) ≤
      ((1312 / 3 : ℝ) * C * R ^ 2 * Real.log X ^ 2 *
        (r + M * X ^ θ - l + ε * X)) / (X ^ θ * Real.log X) ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hS : 0 < X ^ θ * Real.log X := mul_pos (Real.rpow_pos_of_pos hX0 _) hlog
  have hh := macro_fourth_comparison hE hB ha hM hC hX hε hl hlr hr hc hR hV
    hMX hLX hlo hhi hgap
  have heq : (fun x => |movingB E a θ X x - fixedScaleB E θ c X x| ^ 4) =
      fun x => |macroIncrement E a θ X x - increment E (X ^ θ * c) x| ^ 4 /
        (X ^ θ * Real.log X) ^ 2 := by
    funext x
    simp only [movingB, fixedScaleB, dyadicU, macroIncrement, ← sub_div,
      abs_div, div_pow, mul_comm c (X ^ θ), mul_comm (a (x / X)) (X ^ θ), abs_pow, Even.pow_abs (by decide : Even 4)]
    rw [show Real.sqrt (X ^ θ * Real.log X) ^ 4 = (X ^ θ * Real.log X) ^ 2 by
      nlinarith [Real.sq_sqrt hS.le]]
  rw [heq, intervalIntegral.integral_div]
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

/-- Freezing into n cells has an explicit fourth-moment error bound. -/
theorem freezing_fourth_finite
    {E a : ℝ → ℝ} {α θ β C M L X ε : ℝ} {n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β) (hC : 0 ≤ C)
    (hM : 1 ≤ M) (hL : 0 ≤ L) (ha : MacroscopicLengthBounds a M L) (hn : 0 < n)
    (hX : 4 ≤ X) (hε : 0 ≤ ε) (hV : localFourthEnergyWindow E α β C X ε)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2)
    (hlo : (4 * X) ^ α ≤ (1 + L) * X ^ θ / (n : ℝ))
    (hhi : 4 * ((1 + L) * X ^ θ / (n : ℝ)) ≤ (X / 2) ^ β) :
    (∫ x, |movingB E a θ X x - frozenB E a θ n X x| ^ 4
      ∂dyadicProbabilityMeasure X) ≤
      freezeCoefficient C L n * (1 + (n : ℝ) * M * X ^ θ / X + (n : ℝ) * ε) := by
  have hX0 : 0 < X := by linarith
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  let T := ((1312 / 3 : ℝ) * C * ((1 + L) * X ^ θ / n) ^ 2 * Real.log X ^ 2 *
      (X / n + M * X ^ θ + ε * X)) / (X ^ θ * Real.log X) ^ 2
  have heq (j : ℕ) (hj : j < n) :
      EqOn (fun x => |movingB E a θ X x - frozenB E a θ n X x| ^ 4)
        (fun x => |movingB E a θ X x - fixedScaleB E θ (a (cellPoint n j)) X x| ^ 4)
        (uIoc (cellPoint n j * X) (cellPoint n (j + 1) * X)) := by
    intro x hx
    rw [uIoc_of_le (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le)] at hx
    dsimp only
    rw [frozenB_on_cell hn hj hX0 hx]
  have hi (j : ℕ) (hj : j < n) :=
    ((normalized_comparison_integral (θ := θ) (c := a (cellPoint n j)) hE hX0
      ha.1.continuousOn).mono_set (cell_subset hX0 hn hj)).congr
        (fun x hx => (heq j hj hx).symm)
  have hb (j : ℕ) (hj : j < n) :
      (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
        |movingB E a θ X x - frozenB E a θ n X x| ^ 4) ≤ T := by
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall (fun x hx => heq j hj hx))]
    have hu := cellPoint_mem hn hj.le
    have hv := cellPoint_mem hn (Nat.succ_le_of_lt hj)
    have hh := normalized_cell_comparison hE hB ha (by linarith) hC hX hε
      (by nlinarith [hu.1]) (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le)
      (by nlinarith [hv.2]) (ha.2.1 _ hu) (by positivity : 0 < (1 + L) * X ^ θ / (n : ℝ))
      hV hMX hLX hlo hhi (by
        intro x hx
        apply (macro_cell_gap_le ha hL hX0 hn hj x hx).trans
        apply div_le_div_of_nonneg_right _ hn0.le
        nlinarith)
    convert hh using 1
    dsimp [T]
    congr 2
    linear_combination -X * cellPoint_step hn j
  have hh := probability_cell_sum_le hX0 hn hi hb
  apply hh.trans_eq
  dsimp [T, freezeCoefficient]
  field_simp
  <;> ring

private lemma constant_length_bounds {c M L : ℝ} (hc : c ∈ Icc (0 : ℝ) M)
    (hL : 0 ≤ L) : MacroscopicLengthBounds (fun _ : ℝ => c) M L := by
  refine ⟨contDiffOn_const, fun _ _ => hc, ?_⟩
  intro u _
  simpa using hL

private lemma frozen_fourth_finite
    {E a : ℝ → ℝ} {α θ β C M L X ε : ℝ} {n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β) (hC : 0 ≤ C)
    (hM : 1 ≤ M) (hL : 0 ≤ L) (ha : MacroscopicLengthBounds a M L) (hn : 0 < n)
    (hX : 4 ≤ X) (hε : 0 ≤ ε) (hV : localFourthEnergyWindow E α β C X ε)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2)
    (hlo : (4 * X) ^ α ≤ M * X ^ θ) (hhi : 4 * (M * X ^ θ) ≤ (X / 2) ^ β) :
    (∫ x, |frozenB E a θ n X x| ^ 4 ∂dyadicProbabilityMeasure X) ≤
      (1312 / 3 : ℝ) * C * M ^ 2 / Real.log 2 *
        (1 + (n : ℝ) * M * X ^ θ / X + (n : ℝ) * ε) := by
  have hX0 : 0 < X := by linarith
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  let T := ((1312 / 3 : ℝ) * C * (M * X ^ θ) ^ 2 * Real.log X ^ 2 *
      (X / n + M * X ^ θ + ε * X)) / (X ^ θ * Real.log X) ^ 2
  have heq (j : ℕ) (hj : j < n) :
      EqOn (fun x => |frozenB E a θ n X x| ^ 4)
        (fun x => |movingB E (fun _ => a (cellPoint n j)) θ X x - fixedScaleB E θ 0 X x| ^ 4)
        (uIoc (cellPoint n j * X) (cellPoint n (j + 1) * X)) := by
    intro x hx
    rw [uIoc_of_le (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le)] at hx
    dsimp only
    rw [frozenB_on_cell hn hj hX0 hx]
    simp [movingB, fixedScaleB, increment]
  have hi (j : ℕ) (hj : j < n) :=
    ((normalized_comparison_integral (θ := θ) (c := 0) hE hX0
      (continuous_const : Continuous (fun _ : ℝ => a (cellPoint n j))).continuousOn).mono_set
        (cell_subset hX0 hn hj)).congr (fun x hx => (heq j hj hx).symm)
  have hb (j : ℕ) (hj : j < n) :
      (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
        |frozenB E a θ n X x| ^ 4) ≤ T := by
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall (fun x hx => heq j hj hx))]
    have hu := cellPoint_mem hn hj.le
    have hv := cellPoint_mem hn (Nat.succ_le_of_lt hj)
    have hc := ha.2.1 _ hu
    have hh := normalized_cell_comparison hE hB (constant_length_bounds hc hL)
      (by linarith) hC hX hε (by nlinarith [hu.1])
      (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le) (by nlinarith [hv.2])
      (show (0 : ℝ) ∈ Icc 0 M from ⟨le_rfl, by linarith⟩)
      (by positivity : 0 < M * X ^ θ) hV hMX hLX hlo hhi (by
        intro x _
        simp only [sub_zero, abs_mul, abs_of_pos hH, abs_of_nonneg hc.1]
        simpa only [mul_comm M (X ^ θ)] using mul_le_mul_of_nonneg_left hc.2 hH.le)
    convert hh using 1
    dsimp [T]
    congr 2
    linear_combination -X * cellPoint_step hn j
  apply (probability_cell_sum_le hX0 hn hi hb).trans_eq
  dsimp [T]
  field_simp
  <;> ring

/-- Moving lengths in the whole bounded family have one uniform eventual fourth-moment bound. -/
theorem moving_fourth_uniform
    {E : ℝ → ℝ} {α θ β C M L : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : LocalFourthEnergyFor E α β C) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ → ℝ, MacroscopicLengthBounds a M L →
      (∫ x, |movingB E a θ X x| ^ 4 ∂dyadicProbabilityMeasure X) ≤ fourthK C M := by
  obtain ⟨hC, ε, hε, ht, hv⟩ := hV
  filter_upwards [hv, ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    MacroscopicFreezing.scale_conditions hB (show 0 < M by linarith)
      (show 0 < M by linarith) hL (show (0 : ℝ) < 1 by norm_num)] with X hv he hs
  intro a ha
  have hX0 : 0 < X := by linarith [hs.1]
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hlog : 0 < Real.log X := Real.log_pos (by linarith [hs.1])
  have hh := normalized_cell_comparison hE hB ha (by linarith) hC hs.1 (hε X)
    le_rfl (by linarith : X ≤ 2 * X) le_rfl
    (show (0 : ℝ) ∈ Icc 0 M from ⟨le_rfl, by linarith⟩) (by positivity : 0 < M * X ^ θ)
    hv hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 (by
      intro x hx
      have ham := ha.2.1 (x / X)
        ⟨(le_div_iff₀ hX0).2 (by simpa using hx.1), (div_le_iff₀ hX0).2 hx.2⟩
      simp only [sub_zero, abs_mul, abs_of_pos hH, abs_of_nonneg ham.1]
      simpa only [mul_comm M (X ^ θ)] using mul_le_mul_of_nonneg_left ham.2 hH.le)
  simp only [fixedScaleB, increment, zero_mul, add_zero, sub_self, zero_div, sub_zero] at hh
  have hi := normalized_comparison_integral (θ := θ) (c := 0) hE hX0 ha.1.continuousOn
  simp only [fixedScaleB, increment, zero_mul, add_zero, sub_self, zero_div, sub_zero] at hi
  apply (probability_fourth_le hX0 hi).trans
  apply (div_le_div_of_nonneg_right hh (by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)])).trans
  have hlen : 2 * X + M * X ^ θ - X + ε X * X ≤ 3 * X := by
    nlinarith [hs.2.1]
  have hpos : 0 ≤ (1312 / 3 : ℝ) * C * (M * X ^ θ) ^ 2 * Real.log X ^ 2 := by positivity
  apply (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hpos) (sq_nonneg _))
      (by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)])).trans_eq
  dsimp [fourthK]
  field_simp
  <;> ring

/-- Frozen lengths have a uniform eventual fourth-moment bound for every fixed cell count. -/
theorem frozen_fourth_uniform
    {E : ℝ → ℝ} {α θ β C M L : ℝ} {n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : LocalFourthEnergyFor E α β C) (hM : 1 ≤ M) (hL : 0 ≤ L) (hn : 0 < n) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ → ℝ, MacroscopicLengthBounds a M L →
      (∫ x, |frozenB E a θ n X x| ^ 4 ∂dyadicProbabilityMeasure X) ≤ fourthK C M := by
  obtain ⟨hC, ε, hε, ht, hv⟩ := hV
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  filter_upwards [hv, ht.eventually (gt_mem_nhds hd),
    MacroscopicFreezing.scale_conditions hB (show 0 < M by linarith)
      (show 0 < M by linarith) hL hd] with X hv he hs
  intro a ha
  have hh := frozen_fourth_finite hE hB hC hM hL ha hn hs.1 (hε X) hv
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
  have hsmall : 1 + (n : ℝ) * M * X ^ θ / X + (n : ℝ) * ε X ≤ 3 := by
    have h₁ := mul_le_mul_of_nonneg_left hs.2.2.2.2.2.le hn0.le
    have h₂ := mul_le_mul_of_nonneg_left he.le hn0.le
    have heq : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    rw [heq] at h₁ h₂
    simp only [mul_div_assoc, mul_assoc] at h₁ ⊢
    linarith
  apply hh.trans
  have hp : 0 ≤ (1312 / 3 : ℝ) * C * M ^ 2 / Real.log 2 := by
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left hsmall hp).trans_eq (by dsimp [fourthK]; ring)

/-- The eventual freezing threshold is uniform over the bounded family of length functions. -/
theorem freezing_fourth_eventually
    {E : ℝ → ℝ} {α θ β C M L : ℝ} {n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : LocalFourthEnergyFor E α β C) (hM : 1 ≤ M) (hL : 0 ≤ L) (hn : 0 < n) :
    ∀ η : ℝ, 0 < η → ∀ᶠ X : ℝ in atTop,
      ∀ a : ℝ → ℝ, MacroscopicLengthBounds a M L →
        (∫ x, |movingB E a θ X x - frozenB E a θ n X x| ^ 4
          ∂dyadicProbabilityMeasure X) ≤ freezeCoefficient C L n + η := by
  intro η hη
  obtain ⟨hC, ε, hε, ht, hv⟩ := hV
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 ≤ freezeCoefficient C L n := by
    dsimp [freezeCoefficient]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  let δ := η / (2 * (n : ℝ) * (freezeCoefficient C L n + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hc : 0 < (1 + L) / (n : ℝ) := by positivity
  filter_upwards [hv, ht.eventually (gt_mem_nhds hδ),
    MacroscopicFreezing.scale_conditions hB hc (show 0 < M by linarith) hL hδ]
    with X hv he hs
  intro a ha
  have hh := freezing_fourth_finite hE hB hC hM hL ha hn hs.1 (hε X) hv
    hs.2.1 hs.2.2.1
    (by simpa only [div_mul_eq_mul_div] using hs.2.2.2.1)
    (by simpa only [div_mul_eq_mul_div] using hs.2.2.2.2.1)
  have hsmall : 1 + (n : ℝ) * M * X ^ θ / X + (n : ℝ) * ε X ≤ 1 + 2 * n * δ := by
    have h₁ := mul_le_mul_of_nonneg_left hs.2.2.2.2.2.le hn0.le
    have h₂ := mul_le_mul_of_nonneg_left he.le hn0.le
    simp only [mul_div_assoc, mul_assoc] at h₁ ⊢
    nlinarith
  have hδeq : (freezeCoefficient C L n + 1) * (2 * n * δ) = η := by
    dsimp [δ]
    field_simp
  have hlast : freezeCoefficient C L n * (1 + 2 * n * δ) ≤ freezeCoefficient C L n + η := by
    nlinarith [mul_nonneg hn0.le hδ.le]
  exact hh.trans ((mul_le_mul_of_nonneg_left hsmall hD).trans hlast)

end
end D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentFreezing
