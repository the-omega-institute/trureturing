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
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0], u := 9, v := 1, c := (-30), C := (-396), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0], u := 4, v := 1, c := (-10), C := (-58), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3], u := 5, v := 1, c := (-14), C := (-112), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0], u := 15, v := 5, c := (-30), C := (-630), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2], u := 3, v := 1, c := (-6), C := (-30), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0], u := 12, v := 4, c := (-24), C := (-396), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9], u := 15, v := 5, c := (-30), C := (-720), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0], u := 3, v := 1, c := (-6), C := (-24), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2], u := 5, v := 1, c := (-12), C := (-84), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3], u := 6, v := 2, c := (-12), C := (-108), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0], u := 10, v := 4, c := (-16), C := (-202), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7], u := 15, v := 6, c := (-24), C := (-528), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0], u := 5, v := 2, c := (-8), C := (-46), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1], u := 5, v := 2, c := (-8), C := (-48), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-20), C := (-146), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0], u := 10, v := 0, c := (-40), C := (-586), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2], u := 4, v := 0, c := (-16), C := (-98), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0], u := 15, v := 0, c := (-60), C := (-1320), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3], u := 6, v := 0, c := (-24), C := (-222), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0], u := 12, v := 0, c := (-48), C := (-844), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7], u := 15, v := 0, c := (-60), C := (-1380), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-15), C := (-87), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0], u := 9, v := 0, c := (-36), C := (-474), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-21), C := (-183), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5], u := 12, v := 0, c := (-48), C := (-876), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-12), C := (-54), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-12), C := (-52), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-14), C := (-80), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-20), C := (-172), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-11), C := (-49), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-11), C := (-47), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0], u := 4, v := 0, c := (-13), C := (-73), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2], u := 6, v := 0, c := (-19), C := (-161), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1], u := 3, v := 0, c := (-10), C := (-44), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1], u := 3, v := 0, c := (-9), C := (-39), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
