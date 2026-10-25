import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Exact transient slicing and directional FTC checks. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped MeasureTheory Interval

namespace CFMPSimplexDirection435Transient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem sections_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {S : Set (α × β)} {f : α × β → E}
    (hS : MeasurableSet S) (hf : IntegrableOn f S (μ.prod ν)) :
    (∫ z in S, f z ∂(μ.prod ν)) =
      ∫ y, ∫ x in {x : α | (x,y) ∈ S}, f (x,y) ∂μ ∂ν := by
  classical
  calc
    (∫ z in S, f z ∂(μ.prod ν)) = ∫ z, S.indicator f z ∂(μ.prod ν) :=
      (integral_indicator hS).symm
    _ = ∫ y, ∫ x, S.indicator f (x,y) ∂μ ∂ν :=
      integral_prod_symm _ (hf.integrable_indicator hS)
    _ = ∫ y, ∫ x in {x : α | (x,y) ∈ S}, f (x,y) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards with y
      change (∫ x, ({x : α | (x,y) ∈ S}).indicator (fun x => f (x,y)) x ∂μ) = _
      exact integral_indicator (hS.preimage measurable_prodMk_right)

def triangle (a : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ a}

theorem triangle_compact (a : ℝ) : IsCompact (triangle a) := by
  have heq : triangle a = (Icc 0 a ×ˢ Icc 0 a) ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ a} := by
    ext z
    simp only [triangle, mem_setOf_eq, mem_inter_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨hx,hy,hxy⟩
      exact ⟨⟨⟨hx,by linarith⟩,⟨hy,by linarith⟩⟩,hxy⟩
    · rintro ⟨⟨⟨hx,_⟩,⟨hy,_⟩⟩,hxy⟩
      exact ⟨hx,hy,hxy⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const)

theorem triangle_section (a y : ℝ) :
    {x : ℝ | (x,y) ∈ triangle a} =
      if y ∈ Icc 0 a then Icc 0 (a-y) else ∅ := by
  classical
  ext x
  split_ifs with hy
  · simp only [triangle, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨hx,_,hxy⟩; exact ⟨hx,by linarith⟩
    · rintro ⟨hx,hxy⟩; exact ⟨hx,hy.1,by linarith⟩
  · simp only [triangle, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx hy0 hxy
    exact hy ⟨hy0,by linarith⟩

theorem triangle_iterated (a : ℝ) (ha : 0 ≤ a) (D : ℝ × ℝ → E)
    (hD : ContinuousOn D (triangle a)) :
    (∫ z in triangle a, D z) =
      ∫ y in (0 : ℝ)..a, ∫ x in (0 : ℝ)..(a-y), D (x,y) := by
  classical
  have hK := triangle_compact a
  have hInt : IntegrableOn D (triangle a) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact hK hD
  have hs (y : ℝ) :
      (∫ x in {x : ℝ | (x,y) ∈ triangle a}, D (x,y)) =
      (Icc 0 a).indicator (fun y => ∫ x in Icc 0 (a-y), D (x,y)) y := by
    rw [triangle_section]
    by_cases hy : y ∈ Icc 0 a <;> simp [hy]
  calc
    (∫ z in triangle a, D z) =
        ∫ y, ∫ x in {x : ℝ | (x,y) ∈ triangle a}, D (x,y) :=
      sections_snd hK.measurableSet hInt
    _ = ∫ y, (Icc 0 a).indicator (fun y => ∫ x in Icc 0 (a-y), D (x,y)) y := by
      apply integral_congr_ae
      filter_upwards with y
      exact hs y
    _ = ∫ y in Icc 0 a, ∫ x in Icc 0 (a-y), D (x,y) :=
      integral_indicator measurableSet_Icc
    _ = ∫ y in (0 : ℝ)..a, ∫ x in Icc 0 (a-y), D (x,y) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ha]
    _ = ∫ y in (0 : ℝ)..a, ∫ x in (0 : ℝ)..(a-y), D (x,y) := by
      apply intervalIntegral.integral_congr_Ioo_of_le ha
      intro y hy
      change (∫ x in Icc (0 : ℝ) (a-y), D (x,y)) =
        ∫ x in (0 : ℝ)..(a-y), D (x,y)
      rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (sub_nonneg.mpr hy.2.le)]

theorem triangle_directional (a : ℝ) (ha : 0 ≤ a) (P D : ℝ × ℝ → E)
    (hP : ContinuousOn P (triangle a)) (hD : ContinuousOn D (triangle a))
    (hd : ∀ y ∈ Ioo (0 : ℝ) a, ∀ x ∈ Ioo (0 : ℝ) (a-y),
      HasDerivAt (fun t : ℝ => P (t,y)) (D (x,y)) x) :
    (∫ z in triangle a, D z) =
      ∫ y in (0 : ℝ)..a, P (a-y,y)-P (0,y) := by
  rw [triangle_iterated a ha D hD]
  apply intervalIntegral.integral_congr_Ioo_of_le ha
  intro y hy
  have hmap : MapsTo (fun x : ℝ => (x,y)) (Icc 0 (a-y)) (triangle a) := by
    intro x hx
    exact ⟨hx.1,hy.1.le,by linarith [hx.2]⟩
  have hpair : Continuous (fun x : ℝ => (x,y)) :=
    continuous_id.prodMk continuous_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (sub_nonneg.mpr hy.2.le)
    (hP.comp' hpair.continuousOn hmap) (hd y hy)
    (ContinuousOn.intervalIntegrable_of_Icc (sub_nonneg.mpr hy.2.le)
      (hD.comp' hpair.continuousOn hmap))

end CFMPSimplexDirection435Transient
