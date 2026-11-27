import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the integral row difference in moving-lattice exactness. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate (nebeOrderThree)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev Row := Fin 48 → ℤ
local notation "A" => nebeOrderThree
local notation "N" => (1 + A + A ^ 2)
local notation "B" => (1 - A)

abbrev signature : Signature where
  Params := Unit
  State _ := Row
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Row
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ y => Matrix.vecMul y B) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : Row, Matrix.vecMul x N = 0 ↔ ∃ y : Row, R.readout () () y = x

private def firstBasisRow : Row := Pi.single 0 1

private theorem difference_row_ne_zero : Matrix.vecMul firstBasisRow B ≠ 0 := by
  intro h
  rw [firstBasisRow, Matrix.single_one_vecMul] at h
  have hne : B 0 0 ≠ 0 := by decide +kernel
  exact hne (congrFun h 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := (nebeOrderThree_moving_exact (Matrix.vecMul firstBasisRow B)).mpr
    ⟨firstBasisRow, rfl⟩
  obtain ⟨_, hy⟩ := (h (Matrix.vecMul firstBasisRow B)).mp hx
  exact difference_row_ne_zero hy.symm

set_option maxRecDepth 4096 in
def family : Registration arena (type_of% nebeOrderThree_moving_exact) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeOrderThree_moving_exact, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, firstBasisRow, ?_⟩
    change Matrix.vecMul 0 B ≠ Matrix.vecMul firstBasisRow B
    rw [Matrix.zero_vecMul]
    exact Ne.symm difference_row_ne_zero

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeOrderThree_moving_exact (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate.nebeOrderThree_moving_exact.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => Matrix.vecMul y B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificate
