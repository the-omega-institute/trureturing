/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.claim; result=D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted; claim=D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.claim
   digest: A 2-entanglement-breaking map on complex matrices can be indecomposable. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.SignMatrixConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

/-- The affirmative statement of Devendra–Mallick–Sumesh, Open Problem 1. -/
def claim : Prop :=
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ Φ : MatrixMap (Fin a) (Fin b) ℂ, IsKEB 2 Φ → IsDecomposable Φ

/-- An indecomposable 2-entanglement-breaking complex-linear map. -/
theorem devendraMallickSumesh_openProblem1_counterexample :
    ∃ (d : ℕ) (_ : 0 < d) (Φ : MatrixMap (Fin d) (Fin d) ℂ),
      IsKEB 2 Φ ∧ ¬ IsDecomposable Φ :=
  ⟨4194304, by decide, exists_indecomposable_kEB 2 4194304 (by decide) (by decide)⟩

/-- The universal decomposability statement for 2-entanglement-breaking maps is false. -/
theorem devendraMallickSumesh_openProblem1_refuted : ¬ claim := by
  intro h
  obtain ⟨d, hd, Φ, hEB, hInd⟩ := devendraMallickSumesh_openProblem1_counterexample
  exact hInd (h d d hd hd Φ hEB)

end D5.S3.Quantum.Entanglement.EntanglementBreaking
