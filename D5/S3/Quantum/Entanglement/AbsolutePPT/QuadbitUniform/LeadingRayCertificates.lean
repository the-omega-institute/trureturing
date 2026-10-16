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
  · change RayData.Valid { gap := ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 11, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 3, C := 23, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 7, C := 47, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 4, C := 28, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 52, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0], u := 5, v := 2, c := (-2), C := 26, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5], u := 5, v := 2, c := 8, C := 176, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-18), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-5), C := (-13), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-4), C := (-8), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0], u := 3, v := 0, c := (-7), C := (-27), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0], u := 4, v := 0, c := 8, C := 110, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4], u := 4, v := 0, c := 16, C := 190, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 66, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4], u := 6, v := 0, c := (-12), C := (-90), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1], u := 2, v := 0, c := (-2), C := (-2), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0], u := 6, v := 0, c := 12, C := 246, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 46, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 18, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 60, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0], u := 9, v := 0, c := (-30), C := (-384), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-9), C := (-51), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 0, C := 6, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 0, C := 8, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 6, C := 62, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0], u := 6, v := 1, c := 6, C := 168, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-8), C := (-36), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-2), C := 4, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-8), C := (-40), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 1, C := 11, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 1, C := 13, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-6), C := (-20), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0], u := 7, v := 0, c := 2, C := 128, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-2), C := 0, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0], u := 10, v := 0, c := 10, C := 430, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3], u := 4, v := 0, c := 4, C := 58, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0], u := 8, v := 0, c := 8, C := 276, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7], u := 10, v := 0, c := 10, C := 370, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-1), C := 11, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0], u := 6, v := 0, c := 6, C := 156, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-7), C := (-29), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5], u := 8, v := 0, c := 8, C := 244, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 2, C := 16, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
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
