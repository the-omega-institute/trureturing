/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/LeadingRayCertificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/LeadingRayCertificates
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Moment and branch certificates for original ray labels 29 through 91. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.RayMoments

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem leadingRayCertificates (i : Fin 63) :
    (originalRay ⟨29 + i.val, by omega⟩).Valid := by
  fin_cases i
  · change RayData.Valid (![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 3, 11, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0], 2, 0, 2, 18, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 6, 42, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0], 2, 0, 3, 23, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 7, 47, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0], 2, 0, 4, 28, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 8, 52, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0], 5, 2, (-2), 26, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5], 5, 2, 8, 176, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0], 3, 0, (-10), (-42), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2], 3, 0, (-6), (-18), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0], 3, 0, (-9), (-37), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2], 3, 0, (-5), (-13), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0], 3, 0, (-8), (-32), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2], 3, 0, (-4), (-8), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0], 3, 0, (-7), (-27), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2], 3, 0, (-3), (-3), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1], 2, 0, (-4), (-10), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0], 4, 0, 8, 110, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4], 4, 0, 16, 190, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0], 6, 2, 0, 78, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3], 3, 1, 6, 66, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0], 6, 0, (-20), (-170), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4], 6, 0, (-12), (-90), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1], 2, 0, (-2), (-2), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2], 3, 0, 3, 39, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1], 2, 0, 2, 18, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0], 6, 0, 12, 246, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 8, 46, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0], 3, 1, 0, 18, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3], 3, 1, 6, 60, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0], 9, 0, (-30), (-384), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2], 3, 0, (-6), (-24), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0], 3, 0, (-3), (-3), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2], 5, 0, (-9), (-51), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0], 4, 0, 0, 30, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1], 2, 0, 0, 6, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0], 2, 0, 0, 8, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1], 4, 0, 0, 30, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0], 3, 0, 6, 62, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0], 6, 1, 6, 168, 2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0], 4, 0, (-8), (-36), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0], 3, 0, (-2), 4, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2], 5, 0, (-8), (-40), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0], 4, 0, 2, 50, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1], 2, 0, 1, 11, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0], 2, 0, 1, 13, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1], 4, 0, 2, 50, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0], 4, 0, (-6), (-20), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0], 7, 0, 2, 128, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2], 3, 0, (-2), 0, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0], 10, 0, 10, 430, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3], 4, 0, 4, 58, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0], 8, 0, 8, 276, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7], 10, 0, 10, 370, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0], 3, 0, (-1), 11, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0], 6, 0, 6, 156, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2], 5, 0, (-7), (-29), 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5], 8, 0, 8, 244, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0], 4, 0, 4, 70, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1], 2, 0, 2, 16, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0], 2, 0, 2, 18, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]
  · change RayData.Valid (![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1], 4, 0, 4, 70, 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · unfold MomentWitness
      decide +kernel
    · norm_num [branchValid, boundaryCertificate, middleCertificate]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
