/- GID: D5/S3/Quantum/Petz/SymmetricStieltjesSwap
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite symmetric nonnegative double Stieltjes integrals admit a sum-preserving marginal representation. -/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import D5.S3.Quantum.PositiveResolvent.SwapDifferentiation

open Set MeasureTheory Filter
open scoped Topology

namespace D5.S3.Quantum.Petz.SymmetricStieltjesSwap

/-- The finite form of the symmetric-kernel swap identity. Positivity is needed only
to dominate the two partial-fraction summands by the original integrable kernel. -/
theorem symmetric_stieltjes_swap (K : ℝ → ℝ → ℝ)
    (hK : Measurable (Function.uncurry K))
    (hpos : ∀ s t : ℝ, 0 < s → 0 < t → 0 ≤ K s t)
    (hsym : ∀ s t : ℝ, 0 < s → 0 < t → K s t = K t s)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hfin : Integrable (fun p : ℝ × ℝ => K p.1 p.2 / ((x + p.1) * (y + p.2)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) :
    IntegrableOn (fun s : ℝ => (1 / (x + s) + 1 / (y + s)) *
      (∫ t in Ioi 0, K s t / (x + y + s + t))) (Ioi 0) ∧
    (∫ p : ℝ × ℝ, K p.1 p.2 / ((x + p.1) * (y + p.2))
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∫ s in Ioi 0, (1 / (x + s) + 1 / (y + s)) *
        (∫ t in Ioi 0, K s t / (x + y + s + t)) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ × ℝ → ℝ := fun p => K p.1 p.2 / ((x + p.1) * (y + p.2))
  let g : ℝ × ℝ → ℝ := fun p => K p.1 p.2 / ((x + p.1) * (x + y + p.1 + p.2))
  let q : ℝ × ℝ → ℝ := fun p => K p.1 p.2 / ((y + p.2) * (x + y + p.1 + p.2))
  let r : ℝ × ℝ → ℝ := fun p => K p.1 p.2 / ((y + p.1) * (x + y + p.1 + p.2))
  have hsupport : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, 0 < p.1 ∧ 0 < p.2 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hsplit : ∀ᵐ p ∂μ.prod μ, f p = g p + q p := by
    filter_upwards [hsupport] with p hp
    dsimp [f, g, q]
    have hxs : x + p.1 ≠ 0 := (add_pos hx hp.1).ne'
    have hyt : y + p.2 ≠ 0 := (add_pos hy hp.2).ne'
    have hsum : x + y + p.1 + p.2 ≠ 0 := (show 0 < x + y + p.1 + p.2 by linarith [hp.1, hp.2]).ne'
    field_simp [hxs, hyt, hsum]
    <;> ring
  have hgm : Measurable g := by
    exact hK.div ((measurable_const.add measurable_fst).mul
      (((measurable_const.add measurable_const).add measurable_fst).add measurable_snd))
  have hqm : Measurable q := by
    exact hK.div ((measurable_const.add measurable_snd).mul
      (((measurable_const.add measurable_const).add measurable_fst).add measurable_snd))
  have hgn : ∀ᵐ p ∂μ.prod μ, 0 ≤ g p := by
    filter_upwards [hsupport] with p hp
    dsimp [g]
    exact div_nonneg (hpos p.1 p.2 hp.1 hp.2)
      (mul_nonneg (by linarith [hp.1]) (by linarith [hp.1, hp.2]))
  have hqn : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p := by
    filter_upwards [hsupport] with p hp
    dsimp [q]
    exact div_nonneg (hpos p.1 p.2 hp.1 hp.2)
      (mul_nonneg (by linarith [hp.2]) (by linarith [hp.1, hp.2]))
  have hgi : Integrable g (μ.prod μ) := by
    refine hfin.mono_nonneg hgm.aestronglyMeasurable hgn ?_
    filter_upwards [hsplit, hqn] with p hp hq
    linarith
  have hqi : Integrable q (μ.prod μ) := by
    refine hfin.mono_nonneg hqm.aestronglyMeasurable hqn ?_
    filter_upwards [hsplit, hgn] with p hp hg
    linarith
  have hqr : (fun p => q p.swap) =ᵐ[μ.prod μ] r := by
    filter_upwards [hsupport] with p hp
    dsimp [q, r]
    rw [hsym p.2 p.1 hp.2 hp.1]
    congr 2
    ring
  have hri : Integrable r (μ.prod μ) := hqi.swap.congr hqr
  have hgeq (s : ℝ) : (∫ t, g (s, t) ∂μ) =
      (1 / (x + s)) * ∫ t, K s t / (x + y + s + t) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [g]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  have hreq (s : ℝ) : (∫ t, r (s, t) ∂μ) =
      (1 / (y + s)) * ∫ t, K s t / (x + y + s + t) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [r]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  have houter : (fun s => (∫ t, g (s, t) ∂μ) + ∫ t, r (s, t) ∂μ) =
      (fun s => (1 / (x + s) + 1 / (y + s)) *
        ∫ t, K s t / (x + y + s + t) ∂μ) := by
    funext s
    rw [hgeq, hreq, add_mul]
  have hoi := hgi.integral_prod_left.add hri.integral_prod_left
  change Integrable (fun s => (∫ t, g (s, t) ∂μ) + ∫ t, r (s, t) ∂μ) μ at hoi
  rw [houter] at hoi
  refine ⟨hoi, ?_⟩
  change (∫ p, f p ∂μ.prod μ) = _
  calc
    (∫ p, f p ∂μ.prod μ) = (∫ p, g p + q p ∂μ.prod μ) := integral_congr_ae hsplit
    _ = (∫ p, g p ∂μ.prod μ) + ∫ p, q p ∂μ.prod μ := integral_add hgi hqi
    _ = (∫ p, g p ∂μ.prod μ) + ∫ p, r p ∂μ.prod μ := by
      rw [← integral_prod_swap q, integral_congr_ae hqr]
    _ = (∫ s, ∫ t, g (s, t) ∂μ ∂μ) + ∫ s, ∫ t, r (s, t) ∂μ ∂μ := by
      rw [integral_prod g hgi, integral_prod r hri]
    _ = ∫ s, (∫ t, g (s, t) ∂μ) + ∫ t, r (s, t) ∂μ ∂μ :=
      (integral_add hgi.integral_prod_left hri.integral_prod_left).symm
    _ = _ := by rw [houter]

/-- Differentiating a symmetric double Stieltjes transform along a constant-sum
path needs only finiteness at the base parameters. Nearby product integrands are
dominated by four times that base integrand. -/
theorem symmetric_double_swap_hasDerivAt (K : ℝ → ℝ → ℝ)
    (hK : Measurable (Function.uncurry K))
    (hpos : ∀ s t : ℝ, 0 < s → 0 < t → 0 ≤ K s t)
    (hsym : ∀ s t : ℝ, 0 < s → 0 < t → K s t = K t s)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hfin : Integrable (fun p : ℝ × ℝ => K p.1 p.2 / ((x + p.1) * (y + p.2)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) :
    IntegrableOn (fun s : ℝ => (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) *
      (∫ t in Ioi 0, K s t / (x + y + s + t))) (Ioi 0) ∧
    HasDerivAt (fun h : ℝ => ∫ p : ℝ × ℝ,
      K p.1 p.2 / ((x + h + p.1) * (y - h + p.2))
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
      (-(y - x) * ∫ s in Ioi 0,
        (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) *
          (∫ t in Ioi 0, K s t / (x + y + s + t))) 0 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let d : ℝ → ℝ := fun s => ∫ t in Ioi 0, K s t / (x + y + s + t)
  have hdm : Measurable d := by
    have hm : Measurable (fun p : ℝ × ℝ => K p.1 p.2 / (x + y + p.1 + p.2)) :=
      hK.div (((measurable_const.add measurable_const).add measurable_fst).add measurable_snd)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hbase := symmetric_stieltjes_swap K hK hpos hsym hx hy hfin
  have hderiv := D5.S3.Quantum.PositiveResolvent.SwapDifferentiation.signed_swap_hasDerivAt
    hx hy hdm hbase.1
  refine ⟨hderiv.1, hderiv.2.congr_of_eventuallyEq ?_⟩
  have hm : 0 < min x y := lt_min hx hy
  filter_upwards [Ioo_mem_nhds (show -(min x y) / 2 < (0 : ℝ) by linarith)
    (show (0 : ℝ) < min x y / 2 by positivity)] with h hh
  have hxh : 0 < x + h := by linarith [hh.1, min_le_left x y]
  have hyh : 0 < y - h := by linarith [hh.2, min_le_right x y]
  have hsupport : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, 0 < p.1 ∧ 0 < p.2 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hshift : Integrable (fun p : ℝ × ℝ =>
      K p.1 p.2 / ((x + h + p.1) * (y - h + p.2))) (μ.prod μ) := by
    apply (hfin.const_mul 4).mono_nonneg
    · exact (hK.div ((measurable_const.add measurable_fst).mul
        (measurable_const.add measurable_snd))).aestronglyMeasurable
    · filter_upwards [hsupport] with p hp
      exact div_nonneg (hpos p.1 p.2 hp.1 hp.2)
        (mul_pos (add_pos hxh hp.1) (add_pos hyh hp.2)).le
    · filter_upwards [hsupport] with p hp
      have hA : 0 < x + p.1 := add_pos hx hp.1
      have hB : 0 < y + p.2 := add_pos hy hp.2
      have hC : 0 < x + h + p.1 := add_pos hxh hp.1
      have hD : 0 < y - h + p.2 := add_pos hyh hp.2
      have hAC : x + p.1 ≤ 2 * (x + h + p.1) := by linarith [hh.1, min_le_left x y, hp.1]
      have hBD : y + p.2 ≤ 2 * (y - h + p.2) := by linarith [hh.2, min_le_right x y, hp.2]
      have hden : (x + p.1) * (y + p.2) / 4 ≤ (x + h + p.1) * (y - h + p.2) := by
        nlinarith [mul_le_mul hAC hBD hB.le (by positivity : 0 ≤ 2 * (x + h + p.1))]
      calc
        _ ≤ K p.1 p.2 / (((x + p.1) * (y + p.2)) / 4) :=
          div_le_div_of_nonneg_left (hpos p.1 p.2 hp.1 hp.2) (by positivity) hden
        _ = 4 * (K p.1 p.2 / ((x + p.1) * (y + p.2))) := by rw [div_div_eq_mul_div]; ring
  have hswap := (symmetric_stieltjes_swap K hK hpos hsym hxh hyh hshift).2
  simpa only [show x + h + (y - h) = x + y by ring, d, μ] using hswap

end D5.S3.Quantum.Petz.SymmetricStieltjesSwap
