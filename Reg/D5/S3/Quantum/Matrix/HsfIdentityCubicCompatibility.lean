import D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit attempts with actual typed readouts and whole-family variation. -/
set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility
noncomputable section
universe u v

namespace positive_direction_bound
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
    R.readout () () (iteratedDeriv 3 (curve U H K) 0, iteratedDeriv 2 (curve U H K) 0)
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
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.positive_direction_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.positive_direction_bound.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.positive_direction_bound.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.positive_direction_bound.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.positive_direction_bound.family
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
end positive_direction_bound

namespace signed_derivative_transfer
private abbrev signature : Signature where
  Params := Unit
  State _ := (ℝ × ℝ) × (ℝ × ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1.1 = 4*s.2.1 ∧ s.1.2 = 12*s.2.1+8*s.2.2) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (U H K : Matrix n n ℂ),
    K.IsHermitian →
    let g := curve U ((1/2 : ℝ) • (U+H)) ((1/2 : ℝ) • (1+K))
    R.readout () () ((iteratedDeriv 2 (curve U H K) 0,iteratedDeriv 3 (curve U H K) 0),
      (iteratedDeriv 2 g 0,iteratedDeriv 3 g 0))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp)
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
  refine ⟨(), ((0,0),(0,0)), ((1,0),(0,0)), ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.signed_derivative_transfer.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.signed_derivative_transfer.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.signed_derivative_transfer.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.signed_derivative_transfer.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.signed_derivative_transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1.1 = 4*s.2.1 ∧ s.1.2 = 12*s.2.1+8*s.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end signed_derivative_transfer

namespace identity_cubic_compatibility
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
  realize signature (fun _ _ s => 0 ≤ s.1 ∧ |s.2| ≤ 5*s.1) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (U H K : Matrix n n ℂ),
    K.IsHermitian → (U+H).PosSemidef → (U-H).PosSemidef →
    (1+K).PosSemidef → (1-K).PosSemidef →
    R.readout () () (iteratedDeriv 2 (curve U H K) 0,iteratedDeriv 3 (curve U H K) 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp) (by simp) (by simp) (by simp) (by simp)
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
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.identity_cubic_compatibility.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.identity_cubic_compatibility.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.identity_cubic_compatibility.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.identity_cubic_compatibility.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.identity_cubic_compatibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => 0 ≤ s.1 ∧ |s.2| ≤ 5*s.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end identity_cubic_compatibility

namespace sharp5
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
  realize signature (fun _ _ s => s.1 = 24 ∧ s.2 = 120) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (iteratedDeriv 2 (curve (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1)) 0,
    iteratedDeriv 3 (curve (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1)) 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h
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
  refine ⟨(), (24,120), (0,0), ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.sharp5)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.sharp5, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.sharp5) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.sharp5.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility.sharp5.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = 24 ∧ s.2 = 120) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end sharp5

end Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility
