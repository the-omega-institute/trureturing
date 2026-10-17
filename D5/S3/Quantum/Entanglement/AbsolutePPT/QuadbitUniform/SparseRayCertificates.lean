/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SparseRayCertificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SparseRayCertificates
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Moment and branch certificates for original ray labels 0 through 28. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.RayMoments

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem sparseRayCertificates (i : Fin 29) :
    (originalRay ⟨0 + i.val, by omega⟩).Valid := by
  fin_cases i
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], 1, 0, (-2), (-2), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], 1, 0, (-1), (-1), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 0, 0, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], 1, 0, 0, 2, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 2, 8, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0], 1, 0, 1, 5, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 6, 42, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0], 3, 0, 3, 39, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 3, 9, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0], 3, 0, 5, 55, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 4, 12, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0], 5, 0, 10, 170, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5], 5, 0, 20, 280, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0], 2, 1, (-2), (-4), 1)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3], 3, 2, 0, 0, 3)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0], 8, 0, (-32), (-376), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5], 9, 0, (-36), (-504), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0], 5, 0, (-19), (-137), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1], 2, 0, (-8), (-24), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0], 5, 0, (-17), (-121), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1], 2, 0, (-7), (-21), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0], 5, 0, (-15), (-105), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1], 2, 0, (-6), (-18), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0], 2, 0, (-6), (-16), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2], 5, 0, (-15), (-105), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0], 2, 0, (-5), (-13), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1], 3, 0, (-8), (-32), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0], 2, 0, (-4), (-10), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1], 3, 0, (-6), (-24), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
