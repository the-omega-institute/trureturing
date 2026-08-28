/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionNormalizerCertificate
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionNormalizerCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fivefold stabilizers are certified as normalizers of the explicit five-cycle subgroups. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionNormalizerCertificateParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

set_option maxHeartbeats 4000000 in
-- The normalizer certificate enumerates each fivefold axis and group element.
set_option maxRecDepth 100000 in
theorem chartFivefoldNormalizerCertificate :
    ∀ p : ChartFivefoldAxis,
      Fintype.card (chartFiveCycleSubgroup p) = 5 ∧
        ∀ g : IcosahedralGroup,
          g ∈ MulAction.stabilizer IcosahedralGroup p.1 ↔
            g ∈ Subgroup.normalizer (chartFiveCycleSubgroup p : Set IcosahedralGroup) := by
  change ∀ p, chartFivefoldNormalizerCertificateAt p
  intro p
  fin_cases p
  all_goals
    first
    | exact chartFivefoldNormalizerCertificateAt19
    | exact chartFivefoldNormalizerCertificateAt20
    | exact chartFivefoldNormalizerCertificateAt23
    | exact chartFivefoldNormalizerCertificateAt25
    | exact chartFivefoldNormalizerCertificateAt28
    | exact chartFivefoldNormalizerCertificateAt29

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
