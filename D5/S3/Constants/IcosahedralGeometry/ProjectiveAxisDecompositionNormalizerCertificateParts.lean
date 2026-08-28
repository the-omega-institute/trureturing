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

private theorem certificateAt_of_not_stabilizer_witness
    (p : ChartFivefoldAxis)
    (hcard : Fintype.card (chartFiveCycleSubgroup p) = 5)
    (hwitness : ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup p.1 →
        ∃ h : chartFiveCycleSubgroup p,
          g * h.1 * g⁻¹ ∉ chartFiveCycleSubgroup p) :
    chartFivefoldNormalizerCertificateAt p := by
  refine ⟨hcard, ?_⟩
  intro g
  constructor
  · exact stabilizer_mem_fiveCycleNormalizer p g
  · intro hnormalizer
    by_contra hg
    obtain ⟨h, hh⟩ := hwitness g hg
    rw [Subgroup.mem_normalizer_iff] at hnormalizer
    exact hh ((hnormalizer h.1).mp h.property)

set_option maxHeartbeats 4000000 in
-- The witness search enumerates the 60 group elements at chart axis 19.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerWitnessAt19 :
    ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup
        (⟨19, by decide⟩ : ChartFivefoldAxis).1 →
        ∃ h : chartFiveCycleSubgroup (⟨19, by decide⟩ : ChartFivefoldAxis),
          g * h.1 * g⁻¹ ∉
            chartFiveCycleSubgroup (⟨19, by decide⟩ : ChartFivefoldAxis) := by
  intro g
  fin_cases g <;> decide

set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificateAt19 :
    chartFivefoldNormalizerCertificateAt (⟨19, by decide⟩ : ChartFivefoldAxis) := by
  apply certificateAt_of_not_stabilizer_witness
  · decide
  · exact chartFivefoldNormalizerWitnessAt19

set_option maxHeartbeats 4000000 in
-- The witness search enumerates the 60 group elements at chart axis 20.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerWitnessAt20 :
    ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup
        (⟨20, by decide⟩ : ChartFivefoldAxis).1 →
        ∃ h : chartFiveCycleSubgroup (⟨20, by decide⟩ : ChartFivefoldAxis),
          g * h.1 * g⁻¹ ∉
            chartFiveCycleSubgroup (⟨20, by decide⟩ : ChartFivefoldAxis) := by
  intro g
  fin_cases g <;> decide

set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificateAt20 :
    chartFivefoldNormalizerCertificateAt (⟨20, by decide⟩ : ChartFivefoldAxis) := by
  apply certificateAt_of_not_stabilizer_witness
  · decide
  · exact chartFivefoldNormalizerWitnessAt20

set_option maxHeartbeats 4000000 in
-- The witness search enumerates the 60 group elements at chart axis 23.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerWitnessAt23 :
    ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup
        (⟨23, by decide⟩ : ChartFivefoldAxis).1 →
        ∃ h : chartFiveCycleSubgroup (⟨23, by decide⟩ : ChartFivefoldAxis),
          g * h.1 * g⁻¹ ∉
            chartFiveCycleSubgroup (⟨23, by decide⟩ : ChartFivefoldAxis) := by
  intro g
  fin_cases g <;> decide

set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificateAt23 :
    chartFivefoldNormalizerCertificateAt (⟨23, by decide⟩ : ChartFivefoldAxis) := by
  apply certificateAt_of_not_stabilizer_witness
  · decide
  · exact chartFivefoldNormalizerWitnessAt23

set_option maxHeartbeats 4000000 in
-- The witness search enumerates the 60 group elements at chart axis 25.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerWitnessAt25 :
    ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup
        (⟨25, by decide⟩ : ChartFivefoldAxis).1 →
        ∃ h : chartFiveCycleSubgroup (⟨25, by decide⟩ : ChartFivefoldAxis),
          g * h.1 * g⁻¹ ∉
            chartFiveCycleSubgroup (⟨25, by decide⟩ : ChartFivefoldAxis) := by
  intro g
  fin_cases g <;> decide

set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificateAt25 :
    chartFivefoldNormalizerCertificateAt (⟨25, by decide⟩ : ChartFivefoldAxis) := by
  apply certificateAt_of_not_stabilizer_witness
  · decide
  · exact chartFivefoldNormalizerWitnessAt25

set_option maxHeartbeats 4000000 in
-- The witness search enumerates the 60 group elements at chart axis 28.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerWitnessAt28 :
    ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup
        (⟨28, by decide⟩ : ChartFivefoldAxis).1 →
        ∃ h : chartFiveCycleSubgroup (⟨28, by decide⟩ : ChartFivefoldAxis),
          g * h.1 * g⁻¹ ∉
            chartFiveCycleSubgroup (⟨28, by decide⟩ : ChartFivefoldAxis) := by
  intro g
  fin_cases g <;> decide

set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificateAt28 :
    chartFivefoldNormalizerCertificateAt (⟨28, by decide⟩ : ChartFivefoldAxis) := by
  apply certificateAt_of_not_stabilizer_witness
  · decide
  · exact chartFivefoldNormalizerWitnessAt28

set_option maxHeartbeats 4000000 in
-- The witness search enumerates the 60 group elements at chart axis 29.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerWitnessAt29 :
    ∀ g : IcosahedralGroup,
      g ∉ MulAction.stabilizer IcosahedralGroup
        (⟨29, by decide⟩ : ChartFivefoldAxis).1 →
        ∃ h : chartFiveCycleSubgroup (⟨29, by decide⟩ : ChartFivefoldAxis),
          g * h.1 * g⁻¹ ∉
            chartFiveCycleSubgroup (⟨29, by decide⟩ : ChartFivefoldAxis) := by
  intro g
  fin_cases g <;> decide

set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificateAt29 :
    chartFivefoldNormalizerCertificateAt (⟨29, by decide⟩ : ChartFivefoldAxis) := by
  apply certificateAt_of_not_stabilizer_witness
  · decide
  · exact chartFivefoldNormalizerWitnessAt29

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
