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
  · change RayData.Valid { gap := ![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 20, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 74, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6], u := 6, v := 2, c := 12, C := 294, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0], u := 4, v := 1, c := 2, C := 56, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4], u := 4, v := 1, c := 10, C := 152, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0], u := 5, v := 1, c := (-10), C := (-60), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4], u := 5, v := 1, c := (-2), C := 36, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0], u := 7, v := 2, c := (-10), C := (-64), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6], u := 7, v := 2, c := 2, C := 152, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0], u := 9, v := 3, c := (-10), C := (-54), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8], u := 9, v := 3, c := 6, C := 330, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0], u := 6, v := 2, c := (-8), C := (-44), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5], u := 6, v := 2, c := 2, C := 106, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2], u := 3, v := 1, c := (-2), C := 0, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0], u := 6, v := 2, c := (-4), C := 14, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5], u := 9, v := 3, c := (-6), C := (-6), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0], u := 3, v := 1, c := (-2), C := 4, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1], u := 3, v := 1, c := (-2), C := 2, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3], u := 6, v := 2, c := (-6), C := (-30), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0], u := 6, v := 2, c := (-6), C := (-12), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2], u := 4, v := 1, c := (-2), C := 8, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0], u := 4, v := 1, c := (-2), C := 16, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2], u := 5, v := 1, c := (-14), C := (-108), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0], u := 5, v := 1, c := (-14), C := (-100), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3], u := 7, v := 2, c := (-16), C := (-172), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0], u := 7, v := 2, c := (-16), C := (-154), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4], u := 9, v := 3, c := (-18), C := (-246), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0], u := 9, v := 3, c := (-18), C := (-214), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0], u := 6, v := 2, c := (-12), C := (-98), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8], u := 18, v := 6, c := (-36), C := (-978), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0], u := 6, v := 2, c := (-12), C := (-96), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3], u := 12, v := 4, c := (-24), C := (-402), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4], u := 9, v := 3, c := (-18), C := (-240), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1], u := 3, v := 1, c := (-6), C := (-26), branch := .envelope₂ }
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
