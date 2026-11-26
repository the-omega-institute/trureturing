import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the integral cyclic norm on rows. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate (nebeOrderThree)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private normMatrix normEntry normEntry_eq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate

private abbrev Row := Fin 48 → ℤ
local notation "A" => nebeOrderThree
local notation "N" => (1 + A + A ^ 2)

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
  realize signature (fun _ _ x => Matrix.vecMul x N) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Row, Matrix.vecMul v A = v → ∃ x : Row, R.readout () () x = v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := h 0 (Matrix.zero_vecMul A)
  exact one_ne_zero (congrFun hx 0)

set_option maxRecDepth 4096 in
def family : Registration arena (type_of% nebeOrderThree_fixed_is_norm_image) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeOrderThree_fixed_is_norm_image, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, Pi.single 0 1, ?_⟩
    change Matrix.vecMul 0 N ≠ Matrix.vecMul (Pi.single 0 1) N
    rw [Matrix.zero_vecMul, Matrix.single_one_vecMul]
    intro h
    have h₀ := (congrFun h 0).symm
    change normMatrix 0 0 = 0 at h₀
    have hne : normEntry 0 0 ≠ 0 := by decide +kernel
    exact hne ((normEntry_eq 0 0).symm.trans h₀)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeOrderThree_fixed_is_norm_image (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate.nebeOrderThree_fixed_is_norm_image.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Matrix.vecMul x N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate
