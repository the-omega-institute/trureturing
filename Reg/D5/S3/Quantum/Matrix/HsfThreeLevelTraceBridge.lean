import D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound scalar observations retain each original telescope.
The source-selection reconstruction and escape coordinate are unfinished. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
open _root_.D5.S3.Quantum.Matrix.PsdThreeCubic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge
noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

namespace trace_to_ordered
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 3 → ℝ) (S : Mat) (hS : S.IsHermitian), R.readout () () (closedMomentTrace p S, orderedCubic (fun i j k => orderedCoefficient (p i) (p j) (p k)) S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ => 1) 0 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.trace_to_ordered)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.trace_to_ordered, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.trace_to_ordered) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.trace_to_ordered.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.trace_to_ordered.family
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
end trace_to_ordered

namespace ordered_to_coordinates
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (S : Mat) (hS : S.IsHermitian) (a b c k : ℝ)
    (h0 : h 0 0 0 = 0) (h1 : h 1 1 1 = 0) (h2 : h 2 2 2 = 0)
    (ha0 : h 0 0 1+h 0 1 0+h 1 0 0 = a)
    (ha1 : h 1 1 0+h 1 0 1+h 0 1 1 = a)
    (hb1 : h 1 1 2+h 1 2 1+h 2 1 1 = b)
    (hb2 : h 2 2 1+h 2 1 2+h 1 2 2 = b)
    (hc2 : h 2 2 0+h 2 0 2+h 0 2 2 = c)
    (hc0 : h 0 0 2+h 0 2 0+h 2 0 0 = c)
    (hf : h 0 1 2+h 1 2 0+h 2 0 1 = k/2)
    (hr : h 0 2 1+h 2 1 0+h 1 0 2 = k/2), R.readout () () (orderedCubic h S, cubic a b c k S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ _ _ => 0) 0 (by simp) 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.ordered_to_coordinates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.ordered_to_coordinates, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.ordered_to_coordinates) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.ordered_to_coordinates.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.ordered_to_coordinates.family
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
end ordered_to_coordinates

namespace closed_trace_normal_form
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (S : Mat) (hS : S.IsHermitian), R.readout () () (closedMomentTrace ![p, q, r] S, closedCubic p q r S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_trace_normal_form)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_trace_normal_form, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_trace_normal_form) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.closed_trace_normal_form.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.closed_trace_normal_form.family
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
end closed_trace_normal_form

namespace closed_trace_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (S : Mat) (hS : S.PosSemidef), R.readout () () (0, closedMomentTrace ![p, q, r] S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0 Matrix.PosSemidef.zero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_trace_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_trace_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_trace_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.closed_trace_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge.closed_trace_nonneg.family
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
end closed_trace_nonneg

end
end Reg.D5.S3.Quantum.Matrix.HsfThreeLevelTraceBridge
