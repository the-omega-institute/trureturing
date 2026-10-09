/- GID: D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.claim; result=D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result; claim=D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.claim
   digest: Local trace-norm contraction and conditional information for finite Kraus channels. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
open D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
noncomputable section

def localContraction {n n' : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin n') (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ ρ ρ' : DensityState (Fin n), ρ ≠ ρ' ∧
    r = traceNorm ((of_kraus K K) (CStarMatrix.ofMatrix.symm ρ.1) -
      (of_kraus K K) (CStarMatrix.ofMatrix.symm ρ'.1)) /
      traceNorm (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm ρ'.1)}

def I1 {dA dB n : ℕ}
    (M : Matrix ((Fin dA × Fin dB) × Fin n) ((Fin dA × Fin dB) × Fin n) ℂ) : ℝ :=
  let AB := partialTraceRight M
  let A := partialTraceRight AB
  let B := partialTraceLeft AB
  let BC := partialTraceLeft (M.submatrix
    (fun x : Fin dA × (Fin dB × Fin n) => ((x.1, x.2.1), x.2.2))
    (fun x : Fin dA × (Fin dB × Fin n) => ((x.1, x.2.1), x.2.2)))
  traceNorm (M - (A ⊗ₖ BC).submatrix
    (fun x : (Fin dA × Fin dB) × Fin n => (x.1.1, (x.1.2, x.2)))
    (fun x : (Fin dA × Fin dB) × Fin n => (x.1.1, (x.1.2, x.2)))) -
    traceNorm (AB - A ⊗ₖ B)

def claim : Prop :=
  ∀ (n n' : ℕ),
  ∀ (ι : Type) [Fintype ι] (K : ι → Matrix (Fin n') (Fin n) ℂ),
  (∑ i, (K i)ᴴ * K i) = 1 → localContraction K < 1 →
  ∃ η : ℝ, η < 1 ∧ ∀ (dA dB : ℕ),
  ∀ ρ : DensityState ((Fin dA × Fin dB) × Fin n),
    I1 ((of_kraus
      (fun i => (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ⊗ₖ K i)
      (fun i => (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ⊗ₖ K i))
      (CStarMatrix.ofMatrix.symm ρ.1)) ≤ η * I1 (CStarMatrix.ofMatrix.symm ρ.1)

end
end D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
