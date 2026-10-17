/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/TrailingRayCertificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/TrailingRayCertificates
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Moment and branch certificates for original ray labels 92 through 141. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.RayMoments

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem trailingRayCertificates (i : Fin 50) :
    (originalRay ⟨92 + i.val, by omega⟩).Valid := by
  fin_cases i
  · change RayData.Valid (![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0], 9, 1, (-30), (-396), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0], 4, 1, (-10), (-58), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3], 5, 1, (-14), (-112), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0], 15, 5, (-30), (-630), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2], 3, 1, (-6), (-30), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0], 12, 4, (-24), (-396), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9], 15, 5, (-30), (-720), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0], 3, 1, (-6), (-24), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2], 5, 1, (-12), (-84), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3], 6, 2, (-12), (-108), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0], 10, 4, (-16), (-202), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7], 15, 6, (-24), (-528), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0], 5, 2, (-8), (-46), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1], 5, 2, (-8), (-48), 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0], 5, 0, (-20), (-146), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0], 10, 0, (-40), (-586), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2], 4, 0, (-16), (-98), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0], 15, 0, (-60), (-1320), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3], 6, 0, (-24), (-222), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0], 12, 0, (-48), (-844), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7], 15, 0, (-60), (-1380), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0], 4, 0, (-15), (-87), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0], 9, 0, (-36), (-474), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2], 6, 0, (-21), (-183), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5], 12, 0, (-48), (-876), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0], 6, 0, (-24), (-210), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1], 3, 0, (-12), (-54), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0], 3, 0, (-12), (-52), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1], 6, 0, (-24), (-210), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0], 4, 0, (-14), (-80), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2], 6, 0, (-20), (-172), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0], 6, 0, (-22), (-190), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1], 3, 0, (-11), (-49), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0], 3, 0, (-11), (-47), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1], 6, 0, (-22), (-190), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0], 4, 0, (-13), (-73), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2], 6, 0, (-19), (-161), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0], 6, 0, (-20), (-170), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1], 3, 0, (-10), (-44), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0], 3, 0, (-10), (-42), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1], 6, 0, (-20), (-170), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0], 4, 0, (-12), (-66), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2], 6, 0, (-18), (-150), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0], 6, 0, (-18), (-150), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1], 3, 0, (-9), (-39), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0], 3, 0, (-9), (-37), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1], 6, 0, (-18), (-150), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1], 3, 0, (-9), (-37), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2], 6, 0, (-18), (-150), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1], 4, 0, (-12), (-66), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
