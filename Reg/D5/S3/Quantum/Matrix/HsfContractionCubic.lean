import D5.S3.Quantum.Matrix.HsfContractionCubic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit attempts with actual typed readouts and whole-family variation. -/
set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Matrix.HsfContractionCubic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Reg.D5.S3.Quantum.Matrix.HsfContractionCubic
noncomputable section
universe u v

namespace coefficient_gap_identity
private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A B K : Matrix n n ℂ),
    A.IsHermitian → B.IsHermitian → K.IsHermitian → R.readout () ()
    (144*(2*HsfQubitMixedCubic.coefficient2 (A+B) A K-6*HsfQubitMixedCubic.coefficient3 (A+B) A K),
     WeightedTraceGram.traceGram A (1-K) (words A B K) HsfContractionGrams.M00+
     WeightedTraceGram.traceGram A K (words A B K) HsfContractionGrams.M01+
     WeightedTraceGram.traceGram B (1-K) (words A B K) HsfContractionGrams.M10+
     WeightedTraceGram.traceGram B K (words A B K) HsfContractionGrams.M11)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp) (by simp) (by simp)
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
  refine ⟨(), (0,0), (0,1), ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_identity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_identity.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_identity.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_identity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end coefficient_gap_identity

namespace coefficient_gap_nonneg
private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (U H K : Matrix n n ℂ),
    H.PosSemidef → (U-H).PosSemidef → K.PosSemidef → (1-K).PosSemidef →
    R.readout () () (6*HsfQubitMixedCubic.coefficient3 U H K, 2*HsfQubitMixedCubic.coefficient2 U H K)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp) (by simp) (by simp) (by simp)
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
  refine ⟨(), (0,0), (1,0), ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_nonneg.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_nonneg.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_nonneg.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfContractionCubic.coefficient_gap_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end coefficient_gap_nonneg

end Reg.D5.S3.Quantum.Matrix.HsfContractionCubic
