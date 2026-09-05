/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionNormalizerCertificateParts
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionNormalizerCertificateParts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Small witnesses certify each fivefold-axis normalizer without a nested finite proof tree. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionOrbitCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

def chartFivefoldNormalizerCertificateAt (p : ChartFivefoldAxis) : Prop :=
  Fintype.card (chartFiveCycleSubgroup p) = 5 ∧
    ∀ g : IcosahedralGroup,
      g ∈ MulAction.stabilizer IcosahedralGroup p.1 ↔
        g ∈ Subgroup.normalizer (chartFiveCycleSubgroup p : Set IcosahedralGroup)

private theorem stabilizer_mem_fiveCycleNormalizer
    (p : ChartFivefoldAxis) (g : IcosahedralGroup)
    (hg : g ∈ MulAction.stabilizer IcosahedralGroup p.1) :
    g ∈ Subgroup.normalizer (chartFiveCycleSubgroup p : Set IcosahedralGroup) := by
  change g • p.1 = p.1 at hg
  have hginv : g⁻¹ • p.1 = p.1 := by
    calc
      g⁻¹ • p.1 = g⁻¹ • (g • p.1) := congrArg (g⁻¹ • ·) hg.symm
      _ = p.1 := inv_smul_smul g p.1
  rw [Subgroup.mem_normalizer_iff]
  intro h
  change (h • p.1 = p.1 ∧ h ^ 5 = 1) ↔
    ((g * h * g⁻¹) • p.1 = p.1 ∧ (g * h * g⁻¹) ^ 5 = 1)
  constructor
  · rintro ⟨hhfix, hhpow⟩
    constructor
    · simp only [mul_smul, hginv, hhfix, hg]
    · calc
        (g * h * g⁻¹) ^ 5 = g * h ^ 5 * g⁻¹ := conj_pow
        _ = 1 := by rw [hhpow]; group
  · rintro ⟨hconjfix, hconjpow⟩
    constructor
    · have hfix := congrArg (fun q => g⁻¹ • q) hconjfix
      simpa only [mul_smul, hginv, inv_smul_smul] using hfix
    · calc
        h ^ 5 = g⁻¹ * (g * h ^ 5 * g⁻¹) * g := by group
        _ = g⁻¹ * (g * h * g⁻¹) ^ 5 * g := by rw [conj_pow]
        _ = 1 := by rw [hconjpow]; group

set_option maxHeartbeats 4000000 in
-- One five-cycle per fivefold axis certifies that its chart fixed point is unique.
set_option maxRecDepth 100000 in
private theorem chartFiveCycleUniqueFixedPoint :
    ∀ p : ChartFivefoldAxis,
      ∃ h : chartFiveCycleSubgroup p,
        ∀ q : AxisChart, h.1 • q = q → q = p.1 := by
  intro p
  fin_cases p
  · refine ⟨⟨evaluateAlternatingWord [0, 3, 0], by decide⟩, ?_⟩
    decide
  · refine ⟨⟨evaluateAlternatingWord [1, 3], by decide⟩, ?_⟩
    decide
  · refine ⟨⟨evaluateAlternatingWord [0, 2, 1], by decide⟩, ?_⟩
    decide
  · refine ⟨⟨evaluateAlternatingWord [0, 3, 3], by decide⟩, ?_⟩
    decide
  · refine ⟨⟨evaluateAlternatingWord [2], by decide⟩, ?_⟩
    decide
  · refine ⟨⟨evaluateAlternatingWord [0, 2], by decide⟩, ?_⟩
    decide

private theorem fiveCycleNormalizer_mem_stabilizer
    (p : ChartFivefoldAxis) (g : IcosahedralGroup)
    (hg : g ∈ Subgroup.normalizer
      (chartFiveCycleSubgroup p : Set IcosahedralGroup)) :
    g ∈ MulAction.stabilizer IcosahedralGroup p.1 := by
  change g • p.1 = p.1
  obtain ⟨h, hfixed⟩ := chartFiveCycleUniqueFixedPoint p
  apply hfixed
  rw [Subgroup.mem_normalizer_iff] at hg
  have hconj : g⁻¹ * h.1 * g ∈ chartFiveCycleSubgroup p := by
    apply (hg (g⁻¹ * h.1 * g)).mpr
    convert h.property using 1 <;> group
  change (g⁻¹ * h.1 * g) • p.1 = p.1 ∧
    (g⁻¹ * h.1 * g) ^ 5 = 1 at hconj
  calc
    h.1 • (g • p.1) = (h.1 * g) • p.1 := (mul_smul h.1 g p.1).symm
    _ = (g * (g⁻¹ * h.1 * g)) • p.1 := by
      apply congrArg (fun k : IcosahedralGroup => k • p.1)
      group
    _ = g • ((g⁻¹ * h.1 * g) • p.1) := mul_smul g (g⁻¹ * h.1 * g) p.1
    _ = g • p.1 := congrArg (g • ·) hconj.1

private theorem certificateAt_of_card
    (p : ChartFivefoldAxis)
    (hcard : Fintype.card (chartFiveCycleSubgroup p) = 5) :
    chartFivefoldNormalizerCertificateAt p := by
  refine ⟨hcard, ?_⟩
  intro g
  exact ⟨stabilizer_mem_fiveCycleNormalizer p g,
    fiveCycleNormalizer_mem_stabilizer p g⟩

set_option maxRecDepth 100000 in
private theorem chartFiveCycleSubgroup_card (p : ChartFivefoldAxis) :
    Fintype.card (chartFiveCycleSubgroup p) = 5 := by
  fin_cases p <;> decide

theorem chartFivefoldNormalizerCertificateAtAll (p : ChartFivefoldAxis) :
    chartFivefoldNormalizerCertificateAt p :=
  certificateAt_of_card p (chartFiveCycleSubgroup_card p)

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
