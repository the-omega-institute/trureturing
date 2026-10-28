import D5.S3.Quantum.Matrix.WeightedTraceGram
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit attempts with actual typed readouts and whole-family variation. -/
set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Matrix.WeightedTraceGram
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Reg.D5.S3.Quantum.Matrix.WeightedTraceGram
noncomputable section
universe u v

namespace weighted_traceGram_nonneg
private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def actual : Realization signature :=
  realize signature (fun _ _ s => 0 ≤ s) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {m : Type v} [Fintype m] [DecidableEq m]
    (L T : Matrix n n ℂ) (q : m → Matrix n n ℂ) (M : Matrix m m ℝ),
    L.PosSemidef → T.PosSemidef → M.PosSemidef →
    R.readout () () (traceGram L T q M)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) (m := ULift.{v} Unit) 0 0 (fun _ => 0) 0
    (by simp) (by simp) (by simp)
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
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.WeightedTraceGram.weighted_traceGram_nonneg.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.WeightedTraceGram.weighted_traceGram_nonneg.{u,v}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.WeightedTraceGram.weighted_traceGram_nonneg.{u,v}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.WeightedTraceGram.weighted_traceGram_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.WeightedTraceGram.weighted_traceGram_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => 0 ≤ s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end weighted_traceGram_nonneg

end Reg.D5.S3.Quantum.Matrix.WeightedTraceGram
