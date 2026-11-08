import D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity
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

namespace Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity
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

namespace p396_identity
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q r : ℝ), R.readout () () (p396 p q r, p*q*r*(Q p q r)^2*(p-q)^2*(q-r)^2*(r-p)^2*positiveCertificate p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_identity, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity.p396_identity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity.p396_identity.family
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
end p396_identity

namespace p396_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), R.readout () () (0, p396 p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity.p396_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity.p396_nonneg.family
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
end p396_nonneg

namespace p396_pos
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p), R.readout () () (0, p396 p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 1), (1, 0), ?_⟩
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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_pos, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_pos) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity.p396_pos.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity.p396_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end p396_pos

end
end Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity
