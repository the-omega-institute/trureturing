/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/MiddleRayCertificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/MiddleRayCertificates
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Moment and branch certificates for original ray labels 142 through 186. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.RayMoments

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem middleRayCertificates (i : Fin 45) :
    (originalRay ⟨142 + i.val, by omega⟩).Valid := by
  fin_cases i
  · change RayData.Valid (![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0], 3, 1, 0, 20, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3], 3, 1, 6, 74, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0], 6, 2, 0, 78, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6], 6, 2, 12, 294, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0], 4, 1, 2, 56, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4], 4, 1, 10, 152, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0], 5, 1, (-10), (-60), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4], 5, 1, (-2), 36, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0], 7, 2, (-10), (-64), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6], 7, 2, 2, 152, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0], 9, 3, (-10), (-54), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8], 9, 3, 6, 330, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0], 6, 2, (-8), (-44), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5], 6, 2, 2, 106, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2], 3, 1, (-2), 0, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0], 6, 2, (-4), 14, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5], 9, 3, (-6), (-6), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0], 3, 1, (-2), 4, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1], 3, 1, (-2), 2, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0], 12, 4, (-12), (-66), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3], 6, 2, (-6), (-30), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0], 6, 2, (-6), (-12), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3], 12, 4, (-12), (-66), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0], 4, 1, (-2), 14, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2], 4, 1, (-2), 8, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0], 4, 1, (-2), 16, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1], 4, 1, (-2), 14, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0], 5, 1, (-14), (-102), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2], 5, 1, (-14), (-108), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0], 5, 1, (-14), (-100), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1], 5, 1, (-14), (-102), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0], 14, 4, (-32), (-634), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3], 7, 2, (-16), (-172), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0], 7, 2, (-16), (-154), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3], 14, 4, (-32), (-634), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0], 9, 3, (-18), (-222), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4], 9, 3, (-18), (-246), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0], 9, 3, (-18), (-214), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2], 9, 3, (-18), (-222), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0], 6, 2, (-12), (-98), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8], 18, 6, (-36), (-978), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0], 6, 2, (-12), (-96), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3], 12, 4, (-24), (-402), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4], 9, 3, (-18), (-240), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1], 3, 1, (-6), (-26), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
