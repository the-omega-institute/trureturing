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
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], u := 1, v := 0, c := (-2), C := (-2), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := (-1), C := (-1), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 0, C := 0, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 0, C := 2, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 2, C := 8, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 1, C := 5, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 9, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 5, C := 55, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 4, C := 12, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0], u := 5, v := 0, c := 10, C := 170, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5], u := 5, v := 0, c := 20, C := 280, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0], u := 2, v := 1, c := (-2), C := (-4), branch := .envelope₁ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3], u := 3, v := 2, c := 0, C := 0, branch := .bulk }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0], u := 8, v := 0, c := (-32), C := (-376), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5], u := 9, v := 0, c := (-36), C := (-504), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-19), C := (-137), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1], u := 2, v := 0, c := (-8), C := (-24), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0], u := 5, v := 0, c := (-17), C := (-121), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1], u := 2, v := 0, c := (-7), C := (-21), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1], u := 2, v := 0, c := (-6), C := (-18), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0], u := 2, v := 0, c := (-6), C := (-16), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0], u := 2, v := 0, c := (-5), C := (-13), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
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
