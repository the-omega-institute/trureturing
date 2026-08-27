/- GID: D5/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local-sector-preserving dynamics cannot create correlation directions. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Logic.Function.Iterate

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

namespace D5.S3.Quantum.PredictionDepth.LocalDynamicsNoTomography

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m n : Nat} [NeZero m] [NeZero n]

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

theorem local_dynamics_no_tomography
    (heisenberg : BipartiteHermitian m n →ₗ[ℝ] BipartiteHermitian m n)
    (hlocal : ∀ x,
      x ∈ localASector m n ⊔ localBSector m n →
        heisenberg x ∈ localASector m n ⊔ localBSector m n) :
    (∀ t : Nat, ∀ x,
      x ∈ localASector m n ⊔ localBSector m n →
        (heisenberg^[t]) x ∈ localASector m n ⊔ localBSector m n) ∧
      (∀ t : Nat, ∀ x,
        x ∈ localASector m n ⊔ localBSector m n →
        (heisenberg^[t]) x ∈ correlationSector m n →
        (heisenberg^[t]) x = 0) := by
  rcases bipartite_sector_decomposition m n with
    ⟨_, _, hAC, hBC, _, _, _⟩
  have hlocalOrtho :
      localASector m n ⊔ localBSector m n ⟂ correlationSector m n := by
    rw [Submodule.isOrtho_sup_left]
    exact ⟨hAC, hBC⟩
  have hiterate : ∀ t : Nat, ∀ x,
      x ∈ localASector m n ⊔ localBSector m n →
        (heisenberg^[t]) x ∈ localASector m n ⊔ localBSector m n := by
    intro t
    induction t with
    | zero =>
        intro x hx
        simpa using hx
    | succ t ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact hlocal _ (ih x hx)
  constructor
  · exact hiterate
  · intro t x hx hcorr
    have hmember : (heisenberg^[t]) x ∈
        (localASector m n ⊔ localBSector m n) ⊓ correlationSector m n :=
      ⟨hiterate t x hx, hcorr⟩
    have hbot := hlocalOrtho.disjoint.le_bot hmember
    exact hbot

#print axioms local_dynamics_no_tomography

end D5.S3.Quantum.PredictionDepth.LocalDynamicsNoTomography
