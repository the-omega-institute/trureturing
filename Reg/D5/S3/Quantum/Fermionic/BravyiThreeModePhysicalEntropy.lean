import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the physical entropy identity and comparison. -/

namespace Reg.D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy

open _root_.D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy
open _root_.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
open _root_.D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam c p q : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1),
    R.readout () () (vonNeumannEntropy (comparatorOutput h0 h1))
      (vonNeumannEntropy (normalOutput h0 h1 hn))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (lam := 0) (c := 1) (p := 0) (q := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena (type_of% (@comparator_entropy_le_normalOutput)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@comparator_entropy_le_normalOutput, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@comparator_entropy_le_normalOutput) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy.comparator_entropy_le_normalOutput.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace BlockSum

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam c p q : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1),
    let a := (chiral_isHermitian lam c p q).eigenvalues
    let u := (complement_isHermitian lam c q).eigenvalues
    R.readout () () (vonNeumannEntropy (normalOutput h0 h1 hn))
      (-((∑ i, a i * Real.log (a i)) + 2 * (∑ i, u i * Real.log (u i))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (lam := 0) (c := 1) (p := 0) (q := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  exact one_ne_zero (Eq.mp he rfl)

def family : Registration arena (type_of% (@normalOutput_entropy_eq_blocks)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalOutput_entropy_eq_blocks, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalOutput_entropy_eq_blocks) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy.normalOutput_entropy_eq_blocks.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy.BlockSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BlockSum

end

end Reg.D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy
