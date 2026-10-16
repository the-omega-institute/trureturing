/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnsNineFifteen
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnsNineFifteen
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Checked ordered four-column supports whose least column ranges from 9 to 15. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.CofactorCatalog

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open NonnegativeKernelCircuit NonnegativeKernelCofactor
open D5.S3.Arith.Lattices.CofactorKernel (cofactor augment kernel_cross_identity)
open UniformSpectralBound.SharedSpectral
noncomputable section

namespace ScalarCertificate

set_option maxRecDepth 8192 in
def block09 : Fin 84 → Entry :=
  ![(![9,10,11,12], .inr none),
    (![9,10,11,13], .inl (1,0)),
    (![9,10,11,14], .inl (1,0)),
    (![9,10,11,15], .inl (1,0)),
    (![9,10,11,16], .inl (1,0)),
    (![9,10,11,17], .inl (0,1)),
    (![9,10,11,18], .inl (0,1)),
    (![9,10,12,13], .inl (1,0)),
    (![9,10,12,14], .inl (1,0)),
    (![9,10,12,15], .inl (1,0)),
    (![9,10,12,16], .inl (1,0)),
    (![9,10,12,17], .inl (0,1)),
    (![9,10,12,18], .inl (0,1)),
    (![9,10,13,14], .inl (1,0)),
    (![9,10,13,15], .inl (1,0)),
    (![9,10,13,16], .inl (1,0)),
    (![9,10,13,17], .inl (0,1)),
    (![9,10,13,18], .inl (0,1)),
    (![9,10,14,15], .inl (1,0)),
    (![9,10,14,16], .inl (1,0)),
    (![9,10,14,17], .inr (some (false,1,23))),
    (![9,10,14,18], .inl (0,1)),
    (![9,10,15,16], .inl (3,0)),
    (![9,10,15,17], .inl (1,0)),
    (![9,10,15,18], .inl (0,1)),
    (![9,10,16,17], .inl (1,0)),
    (![9,10,16,18], .inl (0,1)),
    (![9,10,17,18], .inl (1,0)),
    (![9,11,12,13], .inl (1,0)),
    (![9,11,12,14], .inl (1,0)),
    (![9,11,12,15], .inl (1,0)),
    (![9,11,12,16], .inl (1,0)),
    (![9,11,12,17], .inl (0,1)),
    (![9,11,12,18], .inl (0,1)),
    (![9,11,13,14], .inl (1,0)),
    (![9,11,13,15], .inl (1,0)),
    (![9,11,13,16], .inl (1,0)),
    (![9,11,13,17], .inl (0,1)),
    (![9,11,13,18], .inl (0,1)),
    (![9,11,14,15], .inl (1,0)),
    (![9,11,14,16], .inl (1,0)),
    (![9,11,14,17], .inr (some (false,1,133))),
    (![9,11,14,18], .inl (0,1)),
    (![9,11,15,16], .inl (3,0)),
    (![9,11,15,17], .inr (some (false,1,134))),
    (![9,11,15,18], .inl (0,1)),
    (![9,11,16,17], .inl (1,0)),
    (![9,11,16,18], .inl (2,1)),
    (![9,11,17,18], .inl (1,0)),
    (![9,12,13,14], .inl (1,2)),
    (![9,12,13,15], .inl (1,2)),
    (![9,12,13,16], .inl (1,0)),
    (![9,12,13,17], .inl (0,1)),
    (![9,12,13,18], .inl (0,1)),
    (![9,12,14,15], .inl (1,2)),
    (![9,12,14,16], .inl (1,0)),
    (![9,12,14,17], .inr (some (false,1,135))),
    (![9,12,14,18], .inl (0,1)),
    (![9,12,15,16], .inl (3,0)),
    (![9,12,15,17], .inr (some (false,3,136))),
    (![9,12,15,18], .inl (0,1)),
    (![9,12,16,17], .inl (1,0)),
    (![9,12,16,18], .inl (2,0)),
    (![9,12,17,18], .inl (1,3)),
    (![9,13,14,15], .inl (1,2)),
    (![9,13,14,16], .inl (1,0)),
    (![9,13,14,17], .inr (some (false,1,137))),
    (![9,13,14,18], .inl (0,1)),
    (![9,13,15,16], .inl (3,0)),
    (![9,13,15,17], .inr (some (false,1,138))),
    (![9,13,15,18], .inl (0,1)),
    (![9,13,16,17], .inr (some (false,1,0))),
    (![9,13,16,18], .inl (2,0)),
    (![9,13,17,18], .inl (0,3)),
    (![9,14,15,16], .inl (3,0)),
    (![9,14,15,17], .inl (0,2)),
    (![9,14,15,18], .inl (0,1)),
    (![9,14,16,17], .inl (0,2)),
    (![9,14,16,18], .inl (2,0)),
    (![9,14,17,18], .inr (some (false,1,21))),
    (![9,15,16,17], .inl (0,2)),
    (![9,15,16,18], .inl (2,0)),
    (![9,15,17,18], .inr (some (false,3,22))),
    (![9,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid09 : ∀ k : Fin 84, CaseValid (block09 k).1 (block09 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align09 : (List.finRange 84).map (fun k => (block09 k).1) = fourTuples 9 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
def block10 : Fin 56 → Entry :=
  ![(![10,11,12,13], .inl (1,0)),
    (![10,11,12,14], .inl (1,0)),
    (![10,11,12,15], .inl (1,0)),
    (![10,11,12,16], .inl (1,0)),
    (![10,11,12,17], .inl (0,1)),
    (![10,11,12,18], .inl (0,1)),
    (![10,11,13,14], .inl (1,0)),
    (![10,11,13,15], .inl (1,0)),
    (![10,11,13,16], .inl (1,0)),
    (![10,11,13,17], .inl (0,1)),
    (![10,11,13,18], .inl (0,1)),
    (![10,11,14,15], .inl (1,0)),
    (![10,11,14,16], .inl (1,0)),
    (![10,11,14,17], .inr (some (false,1,23))),
    (![10,11,14,18], .inl (0,1)),
    (![10,11,15,16], .inl (1,0)),
    (![10,11,15,17], .inr (some (false,1,139))),
    (![10,11,15,18], .inl (0,1)),
    (![10,11,16,17], .inl (1,0)),
    (![10,11,16,18], .inl (2,1)),
    (![10,11,17,18], .inl (1,0)),
    (![10,12,13,14], .inl (1,2)),
    (![10,12,13,15], .inl (1,2)),
    (![10,12,13,16], .inl (1,0)),
    (![10,12,13,17], .inl (0,1)),
    (![10,12,13,18], .inl (0,1)),
    (![10,12,14,15], .inl (1,2)),
    (![10,12,14,16], .inl (1,0)),
    (![10,12,14,17], .inr (some (false,2,23))),
    (![10,12,14,18], .inl (0,1)),
    (![10,12,15,16], .inl (1,0)),
    (![10,12,15,17], .inr (some (false,1,140))),
    (![10,12,15,18], .inl (0,1)),
    (![10,12,16,17], .inl (1,0)),
    (![10,12,16,18], .inl (2,0)),
    (![10,12,17,18], .inl (1,3)),
    (![10,13,14,15], .inl (1,2)),
    (![10,13,14,16], .inl (1,0)),
    (![10,13,14,17], .inr (some (false,1,23))),
    (![10,13,14,18], .inl (0,1)),
    (![10,13,15,16], .inl (1,0)),
    (![10,13,15,17], .inr (some (false,1,141))),
    (![10,13,15,18], .inl (0,1)),
    (![10,13,16,17], .inr (some (false,1,0))),
    (![10,13,16,18], .inl (2,0)),
    (![10,13,17,18], .inl (0,3)),
    (![10,14,15,16], .inl (1,0)),
    (![10,14,15,17], .inr (some (false,1,23))),
    (![10,14,15,18], .inl (0,1)),
    (![10,14,16,17], .inr (some (false,1,23))),
    (![10,14,16,18], .inl (2,0)),
    (![10,14,17,18], .inr (some (false,2,23))),
    (![10,15,16,17], .inl (0,2)),
    (![10,15,16,18], .inl (2,0)),
    (![10,15,17,18], .inr (some (false,1,24))),
    (![10,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid10 : ∀ k : Fin 56, CaseValid (block10 k).1 (block10 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align10 : (List.finRange 56).map (fun k => (block10 k).1) = fourTuples 10 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
def block11 : Fin 35 → Entry :=
  ![(![11,12,13,14], .inl (1,2)),
    (![11,12,13,15], .inl (1,2)),
    (![11,12,13,16], .inl (1,0)),
    (![11,12,13,17], .inl (0,1)),
    (![11,12,13,18], .inl (0,1)),
    (![11,12,14,15], .inl (1,2)),
    (![11,12,14,16], .inl (1,0)),
    (![11,12,14,17], .inl (0,1)),
    (![11,12,14,18], .inl (0,1)),
    (![11,12,15,16], .inl (1,0)),
    (![11,12,15,17], .inl (0,1)),
    (![11,12,15,18], .inl (0,1)),
    (![11,12,16,17], .inl (1,0)),
    (![11,12,16,18], .inl (2,0)),
    (![11,12,17,18], .inl (1,3)),
    (![11,13,14,15], .inl (1,2)),
    (![11,13,14,16], .inl (1,0)),
    (![11,13,14,17], .inl (0,1)),
    (![11,13,14,18], .inl (0,1)),
    (![11,13,15,16], .inl (1,0)),
    (![11,13,15,17], .inl (0,1)),
    (![11,13,15,18], .inl (0,1)),
    (![11,13,16,17], .inr (some (false,1,0))),
    (![11,13,16,18], .inl (2,0)),
    (![11,13,17,18], .inl (0,3)),
    (![11,14,15,16], .inl (1,0)),
    (![11,14,15,17], .inl (0,1)),
    (![11,14,15,18], .inl (0,1)),
    (![11,14,16,17], .inr (some (false,1,25))),
    (![11,14,16,18], .inl (2,0)),
    (![11,14,17,18], .inl (0,3)),
    (![11,15,16,17], .inr (some (false,1,26))),
    (![11,15,16,18], .inl (2,0)),
    (![11,15,17,18], .inl (0,3)),
    (![11,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid11 : ∀ k : Fin 35, CaseValid (block11 k).1 (block11 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align11 : (List.finRange 35).map (fun k => (block11 k).1) = fourTuples 11 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
def block12 : Fin 20 → Entry :=
  ![(![12,13,14,15], .inr none),
    (![12,13,14,16], .inl (1,0)),
    (![12,13,14,17], .inl (0,1)),
    (![12,13,14,18], .inl (0,1)),
    (![12,13,15,16], .inl (1,0)),
    (![12,13,15,17], .inl (0,1)),
    (![12,13,15,18], .inl (0,1)),
    (![12,13,16,17], .inr (some (false,1,0))),
    (![12,13,16,18], .inl (1,0)),
    (![12,13,17,18], .inl (0,3)),
    (![12,14,15,16], .inl (1,0)),
    (![12,14,15,17], .inl (0,1)),
    (![12,14,15,18], .inl (0,1)),
    (![12,14,16,17], .inr (some (false,1,27))),
    (![12,14,16,18], .inl (1,0)),
    (![12,14,17,18], .inl (0,3)),
    (![12,15,16,17], .inr (some (false,1,28))),
    (![12,15,16,18], .inl (1,0)),
    (![12,15,17,18], .inl (0,3)),
    (![12,16,17,18], .inl (3,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid12 : ∀ k : Fin 20, CaseValid (block12 k).1 (block12 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align12 : (List.finRange 20).map (fun k => (block12 k).1) = fourTuples 12 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
def block13 : Fin 10 → Entry :=
  ![(![13,14,15,16], .inl (1,0)),
    (![13,14,15,17], .inl (0,1)),
    (![13,14,15,18], .inl (0,1)),
    (![13,14,16,17], .inr (some (false,1,0))),
    (![13,14,16,18], .inl (1,0)),
    (![13,14,17,18], .inl (0,1)),
    (![13,15,16,17], .inr (some (false,2,0))),
    (![13,15,16,18], .inl (1,0)),
    (![13,15,17,18], .inl (0,1)),
    (![13,16,17,18], .inr (some (true,1,0)))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid13 : ∀ k : Fin 10, CaseValid (block13 k).1 (block13 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align13 : (List.finRange 10).map (fun k => (block13 k).1) = fourTuples 13 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
def block14 : Fin 4 → Entry :=
  ![(![14,15,16,17], .inl (0,1)),
    (![14,15,16,18], .inl (1,0)),
    (![14,15,17,18], .inl (0,1)),
    (![14,16,17,18], .inr (some (true,1,1)))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid14 : ∀ k : Fin 4, CaseValid (block14 k).1 (block14 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align14 : (List.finRange 4).map (fun k => (block14 k).1) = fourTuples 14 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
def block15 : Fin 1 → Entry :=
  ![(![15,16,17,18], .inr (some (true,1,2)))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem valid15 : ∀ k : Fin 1, CaseValid (block15 k).1 (block15 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem align15 : (List.finRange 1).map (fun k => (block15 k).1) = fourTuples 15 := by
  classical
  decide +kernel

end ScalarCertificate
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
