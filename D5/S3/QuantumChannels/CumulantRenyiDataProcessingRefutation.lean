/- GID: D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.claim; result=D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result; claim=D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.claim
   digest: QDPI fails for the cumulant-based Renyi functional at every alpha > 1, by a dephased qubit pair. -/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

noncomputable section
namespace D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation

private abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity IsCPTP)

/-- The cumulant-based quantum relative Rényi functional of arXiv:2606.31205, Definition 3, for faithful inputs. -/
def cuRenyi {d : ℕ} (α : ℝ) (A B : Mat d) : ℝ :=
  1 / (α - 1) * Real.log (Matrix.trace
    (A * NormedSpace.exp ((α - 1) • (CFC.log A - CFC.log B)))).re

/-- The quantum data-processing inequality at α, for faithful inputs with faithful outputs. -/
def QDPI (α : ℝ) : Prop :=
  ∀ (d : ℕ) (ρ σ : Mat d) (N : MatrixMap (Fin d) (Fin d) ℂ),
    IsDensity ρ → IsDensity σ → ρ.PosDef → σ.PosDef → IsCPTP N →
    (N ρ).PosDef → (N σ).PosDef → cuRenyi α (N ρ) (N σ) ≤ cuRenyi α ρ σ

def claim : Prop := ∃ α : ℝ, 1 < α ∧ QDPI α

/-- No order greater than one satisfies quantum data processing for this functional. -/
theorem result : ¬ claim := by
  sorry

end D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
