/- GID: D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local endpoint estimates control freezing errors uniformly over bounded macroscopic lengths. -/

import D5.S3.Arith.Robin.ForwardKernel.LocalVarianceBand
import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
import Mathlib.Analysis.Calculus.MeanValue

namespace D5.S3.Arith.Robin.ForwardKernel.MacroscopicFreezing

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs MacroscopicVarianceDefs MovingLengthCells

noncomputable section

variable {E : ℝ → ℝ} {α θ β : ℝ}

private lemma macro_comparison_bound
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    {a : ℝ → ℝ} {M L X ε l r c R : ℝ}
    (ha : MacroscopicLengthBounds a M L) (hM : 0 ≤ M)
    (hX : 4 ≤ X) (hε : 0 ≤ ε) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * X)
    (hc : c ∈ Icc (0 : ℝ) M) (hR : 0 < R)
    (hV : VarianceWindowBound E α β X ε)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2)
    (hlo : (4 * X) ^ α ≤ R) (hhi : 4 * R ≤ (X / 2) ^ β)
    (hgap : ∀ x ∈ Icc l r, |X ^ θ * (a (x / X) - c)| ≤ R) :
    (∫ x in l..r, (macroIncrement E a θ X x - increment E (X ^ θ * c) x) ^ 2) ≤
      40 * R * Real.log X * (3 * (r + M * X ^ θ - l) + 16 * ε * X) := by
  have hX0 : 0 < X := by linarith
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hxmem (x : ℝ) (hx : x ∈ Icc l r) : x / X ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hX0).2 (by linarith [hx.1]),
      (div_le_iff₀ hX0).2 (by linarith [hx.2])⟩
  have had : DifferentiableOn ℝ a (Icc (1 : ℝ) 2) := ha.1.differentiableOn (by norm_num)
  have hda (x : ℝ) (hx : x ∈ Icc l r) :=
    (had (x / X) (hxmem x hx)).hasDerivWithinAt
  have hcomp (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivWithinAt (fun x => a (x / X))
        (derivWithin a (Icc (1 : ℝ) 2) (x / X) / X) (Icc l r) x := by
    convert (hda x hx).comp x ((hasDerivAt_id x).div_const X).hasDerivWithinAt
      (fun y hy => hxmem y hy) using 1 <;> simp [div_eq_mul_inv, Function.comp_def]
  have hdq (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivWithinAt (fun x => x + X ^ θ * a (x / X))
        (1 + X ^ θ * (derivWithin a (Icc (1 : ℝ) 2) (x / X) / X)) (Icc l r) x :=
    (hasDerivWithinAt_id x _).add ((hcomp x hx).const_mul _)
  have hdp (x : ℝ) (_hx : x ∈ Icc l r) :
      HasDerivWithinAt (fun x => x + X ^ θ * c) 1 (Icc l r) x :=
    ((hasDerivAt_id x).add_const _).hasDerivWithinAt
  have hbound := LocalVarianceBand.local_endpoint_bound hE hB hlr
    (show l ≤ r + M * X ^ θ by nlinarith [mul_nonneg hM hH.le]) hR (by norm_num : (0 : ℝ) < 1 / 2)
    hX hε (by linarith) (by linarith) hlo hhi hV
    (fun x hx => (hdp x hx).continuousWithinAt)
    (fun x hx => (hdq x hx).continuousWithinAt) hdp hdq (by
      intro x hx
      have hd := (abs_le.1 (ha.2.2 (x / X) (hxmem x hx))).1
      have hh := mul_le_mul_of_nonneg_left hd hH.le
      have hh' := (div_le_div_of_nonneg_right hh hX0.le)
      constructor
      · norm_num
      · ring_nf at hh' hLX ⊢
        linarith) (by
      intro x hx
      have hav := ha.2.1 (x / X) (hxmem x hx)
      constructor <;> constructor <;> nlinarith [hx.1, hx.2, hc.1, hc.2, hav.1, hav.2]) (by
      intro x hx
      convert hgap x hx using 1
      congr 1
      ring)
  convert hbound using 1
  · apply intervalIntegral.integral_congr
    intro x _
    dsimp [macroIncrement, increment]
    ring
  · ring

/-- Freezing on n equal blocks has an explicit normalized square-error bound. -/
theorem freezing_bound (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    {a : ℝ → ℝ} {M L X ε : ℝ} {n : ℕ}
    (hM : 1 ≤ M) (hL : 0 ≤ L) (ha : MacroscopicLengthBounds a M L)
    (hn : 0 < n) (hX : 4 ≤ X) (hε : 0 ≤ ε)
    (hV : VarianceWindowBound E α β X ε)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2)
    (hlo : (4 * X) ^ α ≤ (1 + L) * X ^ θ / (n : ℝ))
    (hhi : 4 * ((1 + L) * X ^ θ / (n : ℝ)) ≤ (X / 2) ^ β) :
    freezingError E a θ n X ≤
      120 * (1 + L) * (1 / (n : ℝ) + M * X ^ θ / X) + 640 * (1 + L) * ε := by
  have hX0 : 0 < X := by linarith
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < varianceScale θ X :=
    mul_pos (mul_pos hX0 hH) (Real.log_pos (by linarith))
  have hj (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
        (macroIncrement E a θ X x - increment E (X ^ θ * a (cellPoint n j)) x) ^ 2) ≤
      40 * ((1 + L) * X ^ θ / n) * Real.log X *
        (3 * (X / n + M * X ^ θ) + 16 * ε * X) := by
    have hjn := Finset.mem_range.1 hj
    have hu := cellPoint_mem hn hjn.le
    have hv := cellPoint_mem hn (Nat.succ_le_of_lt hjn)
    have hstep := cellPoint_step hn j
    have hlen : cellPoint n (j + 1) * X + M * X ^ θ - cellPoint n j * X =
        X / n + M * X ^ θ := by linear_combination X * hstep
    rw [← hlen]
    apply macro_comparison_bound hE hB ha (by linarith) hX hε
      (by nlinarith [hu.1]) (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le)
      (by nlinarith [hv.2]) (ha.2.1 _ hu) (by positivity) hV hMX hLX hlo hhi
    intro x hx
    have hxm : x / X ∈ Icc (cellPoint n j) (cellPoint n (j + 1)) :=
      ⟨(le_div_iff₀ hX0).2 (by simpa using hx.1), (div_le_iff₀ hX0).2 hx.2⟩
    have hab := (convex_Icc (1 : ℝ) 2).norm_image_sub_le_of_norm_derivWithin_le
      (ha.1.differentiableOn (by norm_num)) (fun u hu => by
        simpa only [Real.norm_eq_abs] using ha.2.2 u hu) hu
      (show x / X ∈ Icc (1 : ℝ) 2 from ⟨hu.1.trans hxm.1, hxm.2.trans hv.2⟩)
    simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxm.1)] at hab
    have hd : x / X - cellPoint n j ≤ 1 / n := by linarith [hxm.2]
    have hh := mul_le_mul_of_nonneg_left (hab.trans
      (mul_le_mul_of_nonneg_left hd hL)) hH.le
    rw [abs_mul, abs_of_pos hH]
    calc
      _ ≤ X ^ θ * (L * (1 / n)) := hh
      _ ≤ (1 + L) * X ^ θ / n := by
        have : 0 ≤ X ^ θ / (n : ℝ) := by positivity
        calc
          _ = L * (X ^ θ / (n : ℝ)) := by ring
          _ ≤ (1 + L) * X ^ θ / n := by
            ring_nf at this ⊢
            linarith
  have hs := Finset.sum_le_sum hj
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  unfold freezingError
  apply (div_le_iff₀ hS).2
  apply hs.trans
  dsimp [varianceScale]
  apply le_of_eq
  field_simp
  <;> ring

private lemma scale_conditions (hB : ValidBand α θ β)
    {c M L δ : ℝ} (hc : 0 < c) (hM : 0 < M) (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 4 ≤ X ∧ M * X ^ θ ≤ X ∧ L * X ^ θ / X ≤ 1 / 2 ∧
      (4 * X) ^ α ≤ c * X ^ θ ∧ 4 * (c * X ^ θ) ≤ (X / 2) ^ β ∧
      M * X ^ θ / X < δ := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have ht : Tendsto (fun X : ℝ => X ^ θ / X) atTop (𝓝 0) := by
    simpa only [fixedLength, one_mul] using
      FixedLengthCovariance.length_div_tendsto_zero hθ 1
  have hm := ht.const_mul M
  have hl := ht.const_mul L
  simp only [mul_zero] at hm hl
  have hb₁ := FixedLengthCovariance.shifted_band (c := c) (d := 4) (q := 1) (r := 0)
    hB.2.1 hB.2.2.1 hθ hc (by norm_num) (by norm_num) (by norm_num)
  have hb₂ := FixedLengthCovariance.shifted_band (c := c) (d := 1 / 2) (q := 4) (r := 0)
    hB.2.1 hB.2.2.1 hθ hc (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (4 : ℝ), hb₁, hb₂,
    hm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hm.eventually (gt_mem_nhds hδ)] with X hX hb₁ hb₂ hm hl hδX
  have hX0 : 0 < X := by linarith
  simp only [zero_mul, add_zero, one_mul, fixedLength] at hb₁ hb₂
  refine ⟨hX, ?_, ?_, hb₁.1, ?_, ?_⟩
  · have hh : M * X ^ θ / X < 1 := by simpa only [mul_div_assoc] using hm
    exact ((div_lt_one hX0).1 hh).le
  · simpa only [mul_div_assoc] using hl.le
  · convert hb₂.2 using 1 <;> ring
  · simpa only [mul_div_assoc] using hδX

/-- The threshold for freezing accuracy is independent of the bounded length function. -/
theorem freezing_eventually (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {M L : ℝ} {n : ℕ} (hM : 1 ≤ M) (hL : 0 ≤ L) (hn : 0 < n) :
    ∀ η : ℝ, 0 < η → ∀ᶠ X : ℝ in atTop,
      ∀ a : ℝ → ℝ, MacroscopicLengthBounds a M L →
        freezingError E a θ n X ≤ 120 * (1 + L) / (n : ℝ) + η := by
  intro η hη
  have hLp : 0 < 1 + L := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let ε := η / (1280 * (1 + L))
  let δ := η / (240 * (1 + L))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hc : 0 < (1 + L) / (n : ℝ) := by positivity
  filter_upwards [LocalVarianceBand.variance_window_eventually hV ε hε,
    scale_conditions hB hc (show 0 < M by linarith) hL hδ] with X hv hs
  intro a ha
  have hh := freezing_bound hE hB hM hL ha hn hs.1 hε.le hv hs.2.1 hs.2.2.1
    (by simpa only [div_mul_eq_mul_div] using hs.2.2.2.1)
    (by simpa only [div_mul_eq_mul_div] using hs.2.2.2.2.1)
  have herr := mul_le_mul_of_nonneg_left hs.2.2.2.2.2.le (by positivity : 0 ≤ 120 * (1 + L))
  have heq : 120 * (1 + L) * δ + 640 * (1 + L) * ε = η := by
    dsimp [δ, ε]
    field_simp
    <;> ring
  calc
    _ ≤ 120 * (1 + L) * (1 / (n : ℝ) + M * X ^ θ / X) +
        640 * (1 + L) * ε := hh
    _ = 120 * (1 + L) / (n : ℝ) +
        (120 * (1 + L) * (M * X ^ θ / X) + 640 * (1 + L) * ε) := by ring
    _ ≤ 120 * (1 + L) / (n : ℝ) + η := by linarith

/-- All bounded macroscopic lengths satisfy the same eventual square-integral bound. -/
theorem normalized_square_eventually (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β) (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {M L : ℝ} (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ → ℝ, MacroscopicLengthBounds a M L →
      normalizedSquare θ X (macroIncrement E a θ X) ≤ 880 * M := by
  have hM0 : 0 < M := by linarith
  filter_upwards [LocalVarianceBand.variance_window_eventually hV 1 (by norm_num),
    scale_conditions hB hM0 hM0 hL (show (0 : ℝ) < 1 by norm_num)] with X hv hs
  intro a ha
  have hX0 : 0 < X := by linarith [hs.1]
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hS : 0 < varianceScale θ X :=
    mul_pos (mul_pos hX0 hH) (Real.log_pos (by linarith [hs.1]))
  have hh := macro_comparison_bound hE hB ha hM0.le hs.1 (by norm_num : (0 : ℝ) ≤ 1)
    le_rfl (by linarith : X ≤ 2 * X) le_rfl ⟨le_rfl, hM0.le⟩
    (mul_pos hM0 hH) hv hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 (by
      intro x hx
      have ham := ha.2.1 (x / X)
        ⟨(le_div_iff₀ hX0).2 (by simpa using hx.1), (div_le_iff₀ hX0).2 hx.2⟩
      simp only [sub_zero, abs_mul, abs_of_pos hH, abs_of_nonneg ham.1]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left ham.2 hH.le)
  simp only [increment, mul_zero, add_zero, sub_self, sub_zero] at hh
  unfold normalizedSquare
  apply (div_le_iff₀ hS).2
  apply hh.trans
  have hlog : 0 ≤ Real.log X := (Real.log_pos (by linarith [hs.1])).le
  dsimp [varianceScale]
  nlinarith [mul_nonneg (mul_nonneg hM0.le hH.le) hlog,
    mul_le_mul_of_nonneg_left hs.2.1 (mul_nonneg (mul_nonneg hM0.le hH.le) hlog)]

end
end D5.S3.Arith.Robin.ForwardKernel.MacroscopicFreezing
