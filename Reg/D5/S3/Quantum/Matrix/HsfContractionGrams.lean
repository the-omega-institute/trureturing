import D5.S3.Quantum.Matrix.HsfContractionGrams
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit attempts with actual typed readouts and whole-family variation. -/
set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Matrix.HsfContractionGrams
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Reg.D5.S3.Quantum.Matrix.HsfContractionGrams
noncomputable section
attribute [local simp] Matrix.PosSemidef.zero Matrix.PosSemidef.one
universe u v

namespace grams_posSemidef
private abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 8) (Fin 8) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.PosSemidef) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () M00 ∧ R.readout () () M01 ∧
    R.readout () () M10 ∧ R.readout () () M11
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h.1
private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, -1, ?_⟩
  intro he
  have hz : (0 : Matrix (Fin 8) (Fin 8) ℝ).PosSemidef := by simp
  have hn : (-1 : Matrix (Fin 8) (Fin 8) ℝ).PosSemidef := Eq.mp he hz
  have hd := hn.diag_nonneg (i := 0)
  norm_num at hd
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfContractionGrams.grams_posSemidef)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfContractionGrams.grams_posSemidef, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfContractionGrams.grams_posSemidef) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfContractionGrams.grams_posSemidef.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfContractionGrams.grams_posSemidef.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end grams_posSemidef

end

end Reg.D5.S3.Quantum.Matrix.HsfContractionGrams
