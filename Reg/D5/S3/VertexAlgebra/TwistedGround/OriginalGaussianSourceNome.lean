import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome
noncomputable section
open scoped Topology
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianResolvent OriginalGaussianSourceMeans OriginalGaussianSourceNome
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome.original_source_nome
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    R.readout () ℂ ((r : ℂ) * Complex.exp (2 * sourceConstant (Real.sqrt r : ℂ)) / 16)
      (Real.exp (-Real.pi * F (1 - r) / F r) : ℂ) ∧
      0 < Real.exp (-Real.pi * F (1 - r) / F r) ∧
      Real.exp (-Real.pi * F (1 - r) / F r) < 1
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h (r := 1 / 2) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@original_source_nome)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@original_source_nome, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_source_nome) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome.original_source_nome.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome.original_source_nome.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome.original_source_nome
