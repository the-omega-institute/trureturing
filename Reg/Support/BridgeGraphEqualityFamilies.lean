import D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

noncomputable section
universe u_1 u_2 u_3 u_4
namespace Reg.Support.BridgeGraphEqualityFamilies

abbrev PairParams := Σ _ : ℕ, ℕ
abbrev FiveParams := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
abbrev SixParams := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

abbrev Rows (p alpha beta : ℕ) := Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)
abbrev Cols (p alpha beta : ℕ) := Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)

abbrev SourceIndex (p q alpha beta gamma delta : ℕ) :=
  Cols p alpha beta × Rows q gamma delta
abbrev TargetIndex (p q alpha beta gamma delta : ℕ) :=
  Rows p alpha beta × Cols q gamma delta

/-- Each equality is observed on its complete state; zero-dimensional fibers remain in scope. -/
abbrev sourceVectorEqualitySignature : Signature where
  Params := FiveParams
  State p := SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 → ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def sourceVectorEqualityActual : Realization sourceVectorEqualitySignature :=
  realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def sourceVectorEqualityRejected : Realization sourceVectorEqualitySignature :=
  realize sourceVectorEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem sourceVectorEqualityDependence :
    ObservationalDependence sourceVectorEqualitySignature sourceVectorEqualityActual := by
  intro i
  let p : sourceVectorEqualitySignature.Params := ⟨1, ⟨1, ⟨1, ⟨1, 1⟩⟩⟩⟩
  let x : sourceVectorEqualitySignature.State p := 0
  let y : sourceVectorEqualitySignature.State p := fun _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : sourceVectorEqualitySignature.State p => v (⟨Sum.inl 0, 0⟩, ⟨Sum.inl 0, 0⟩)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev annihilatorMatrixEqualitySignature : Signature where
  Params := FiveParams
  State p := Matrix (Fin p.2.2.1 × Fin p.2.2.2.1)
    (SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Matrix (Fin p.2.2.1 × Fin p.2.2.2.1)
    (SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def annihilatorMatrixEqualityActual : Realization annihilatorMatrixEqualitySignature :=
  realize annihilatorMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def annihilatorMatrixEqualityRejected : Realization annihilatorMatrixEqualitySignature :=
  realize annihilatorMatrixEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem annihilatorMatrixEqualityDependence :
    ObservationalDependence annihilatorMatrixEqualitySignature annihilatorMatrixEqualityActual := by
  intro i
  let p : annihilatorMatrixEqualitySignature.Params := ⟨1, ⟨1, ⟨1, ⟨1, 1⟩⟩⟩⟩
  let x : annihilatorMatrixEqualitySignature.State p := 0
  let y : annihilatorMatrixEqualitySignature.State p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : annihilatorMatrixEqualitySignature.State p => v (0, 0) (⟨Sum.inl 0, 0⟩, ⟨Sum.inl 0, 0⟩)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev squarePairMatrixEqualitySignature : Signature where
  Params := PairParams
  State p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def squarePairMatrixEqualityActual : Realization squarePairMatrixEqualitySignature :=
  realize squarePairMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def squarePairMatrixEqualityRejected : Realization squarePairMatrixEqualitySignature :=
  realize squarePairMatrixEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem squarePairMatrixEqualityDependence :
    ObservationalDependence squarePairMatrixEqualitySignature squarePairMatrixEqualityActual := by
  intro i
  let p : squarePairMatrixEqualitySignature.Params := ⟨1, 1⟩
  let x : squarePairMatrixEqualitySignature.State p := 0
  let y : squarePairMatrixEqualitySignature.State p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : squarePairMatrixEqualitySignature.State p => v (0, 0) (0, 0)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev inclusionProductEqualitySignature : Signature where
  Params := Σ _ : Type u_1, Σ _ : Type u_2, Σ _ : Type u_3, Type u_4
  State p := Matrix (p.1 × p.2.2.1) (p.2.1 × p.2.2.2) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Matrix (p.1 × p.2.2.1) (p.2.1 × p.2.2.2) ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def inclusionProductEqualityActual : Realization inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4} :=
  realize inclusionProductEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def inclusionProductEqualityRejected : Realization inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4} :=
  realize inclusionProductEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem inclusionProductEqualityDependence :
    ObservationalDependence inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4} inclusionProductEqualityActual := by
  intro i
  let p : inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4}.Params := ⟨ULift.{u_1} Unit, ⟨ULift.{u_2} Unit, ⟨ULift.{u_3} Unit, ULift.{u_4} Unit⟩⟩⟩
  let x : inclusionProductEqualitySignature.State p := 0
  let y : inclusionProductEqualitySignature.State p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : inclusionProductEqualitySignature.State p => v (⟨()⟩, ⟨()⟩) (⟨()⟩, ⟨()⟩)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev crossMatrixEqualitySignature : Signature where
  Params := FiveParams
  State p := Matrix (TargetIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Matrix (TargetIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def crossMatrixEqualityActual : Realization crossMatrixEqualitySignature :=
  realize crossMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def crossMatrixEqualityRejected : Realization crossMatrixEqualitySignature :=
  realize crossMatrixEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem crossMatrixEqualityDependence :
    ObservationalDependence crossMatrixEqualitySignature crossMatrixEqualityActual := by
  intro i
  let p : crossMatrixEqualitySignature.Params := ⟨1, ⟨1, ⟨1, ⟨1, 1⟩⟩⟩⟩
  let x : crossMatrixEqualitySignature.State p := 0
  let y : crossMatrixEqualitySignature.State p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : crossMatrixEqualitySignature.State p => v (⟨Sum.inl 0, 0⟩, ⟨Sum.inl 0, 0⟩)
    (⟨Sum.inl 0, 0⟩, ⟨Sum.inl 0, 0⟩)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev coefficientVectorEqualitySignature : Signature where
  Params := PairParams
  State p := Fin p.1 × Fin p.2 → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.1 × Fin p.2 → ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientVectorEqualityActual : Realization coefficientVectorEqualitySignature :=
  realize coefficientVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def coefficientVectorEqualityRejected : Realization coefficientVectorEqualitySignature :=
  realize coefficientVectorEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem coefficientVectorEqualityDependence :
    ObservationalDependence coefficientVectorEqualitySignature coefficientVectorEqualityActual := by
  intro i
  let p : coefficientVectorEqualitySignature.Params := ⟨1, 1⟩
  let x : coefficientVectorEqualitySignature.State p := 0
  let y : coefficientVectorEqualitySignature.State p := fun _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : coefficientVectorEqualitySignature.State p => v (0, 0)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev antiDiagonalVectorEqualitySignature : Signature where
  Params := ℕ
  State p := Fin p × Fin (p + 1 + 1) → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p × Fin (p + 1 + 1) → ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def antiDiagonalVectorEqualityActual : Realization antiDiagonalVectorEqualitySignature :=
  realize antiDiagonalVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def antiDiagonalVectorEqualityRejected : Realization antiDiagonalVectorEqualitySignature :=
  realize antiDiagonalVectorEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem antiDiagonalVectorEqualityDependence :
    ObservationalDependence antiDiagonalVectorEqualitySignature antiDiagonalVectorEqualityActual := by
  intro i
  let p : antiDiagonalVectorEqualitySignature.Params := 1
  let x : antiDiagonalVectorEqualitySignature.State p := 0
  let y : antiDiagonalVectorEqualitySignature.State p := fun _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : antiDiagonalVectorEqualitySignature.State p => v (0, 0)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev widthTwoMatrixEqualitySignature : Signature where
  Params := SixParams
  State p := Matrix (TargetIndex p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    (SourceIndex p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Matrix (TargetIndex p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    (SourceIndex p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def widthTwoMatrixEqualityActual : Realization widthTwoMatrixEqualitySignature :=
  realize widthTwoMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def widthTwoMatrixEqualityRejected : Realization widthTwoMatrixEqualitySignature :=
  realize widthTwoMatrixEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem widthTwoMatrixEqualityDependence :
    ObservationalDependence widthTwoMatrixEqualitySignature widthTwoMatrixEqualityActual := by
  intro i
  let p : widthTwoMatrixEqualitySignature.Params := ⟨1, ⟨1, ⟨1, ⟨1, ⟨1, 1⟩⟩⟩⟩⟩
  let x : widthTwoMatrixEqualitySignature.State p := 0
  let y : widthTwoMatrixEqualitySignature.State p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun v : widthTwoMatrixEqualitySignature.State p => v (⟨Sum.inl 0, 0⟩, ⟨Sum.inl 0, 0⟩)
    (⟨Sum.inl 0, 0⟩, ⟨Sum.inl 0, 0⟩)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

end Reg.Support.BridgeGraphEqualityFamilies

open Reg.Support.BridgeGraphEqualityFamilies

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks

@[reducible] def antiDiagonal_kernelArena : Arena where
  signature := antiDiagonalVectorEqualitySignature
  Law R := ∀ (p : ℕ),
    R.readout () p ((pencil p (p + 1)).mulVec (antiDiagonal p)) 0
theorem antiDiagonal_kernelPositive : antiDiagonal_kernelArena.Law antiDiagonalVectorEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernel
theorem antiDiagonal_kernelNegative : ¬ antiDiagonal_kernelArena.Law antiDiagonalVectorEqualityRejected := by
  intro h
  exact h 0

def antiDiagonal_kernelEvidence : Registration antiDiagonal_kernelArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernel)) where
  actual := antiDiagonalVectorEqualityActual
  bridge := Iff.rfl
  variation := ⟨antiDiagonal_kernelPositive, antiDiagonalVectorEqualityRejected, antiDiagonal_kernelNegative⟩
  sensitivity := ⟨fun i => ⟨antiDiagonalVectorEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, antiDiagonal_kernelNegative⟩,
    fun i => nomatch i⟩
  dependence := antiDiagonalVectorEqualityDependence

@[reducible] def widthTwo_block_decompositionArena : Arena where
  signature := widthTwoMatrixEqualitySignature
  Law R := ∀ (p q alpha beta gamma delta : ℕ),
    R.readout () ⟨p, ⟨q, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩⟩
      (widthTwoMatrix p q alpha beta gamma delta)
      ((blockDiagonal' (fun t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
        pencil (blockLength p alpha beta t.1) (blockLength q gamma delta t.2))).submatrix
        (tensorBlockEquiv (fun t => Fin (blockLength p alpha beta t))
          (fun t => Fin (blockLength q gamma delta t + 1)))
        (tensorBlockEquiv (fun t => Fin (blockLength p alpha beta t + 1))
          (fun t => Fin (blockLength q gamma delta t))))
theorem widthTwo_block_decompositionPositive : widthTwo_block_decompositionArena.Law widthTwoMatrixEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decomposition
theorem widthTwo_block_decompositionNegative : ¬ widthTwo_block_decompositionArena.Law widthTwoMatrixEqualityRejected := by
  intro h
  exact h 0 0 0 0 0 0

def widthTwo_block_decompositionEvidence : Registration widthTwo_block_decompositionArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decomposition)) where
  actual := widthTwoMatrixEqualityActual
  bridge := Iff.rfl
  variation := ⟨widthTwo_block_decompositionPositive, widthTwoMatrixEqualityRejected, widthTwo_block_decompositionNegative⟩
  sensitivity := ⟨fun i => ⟨widthTwoMatrixEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, widthTwo_block_decompositionNegative⟩,
    fun i => nomatch i⟩
  dependence := widthTwoMatrixEqualityDependence

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
