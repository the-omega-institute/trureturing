import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CayleyResolvent
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.CayleyResolvent
open _root_.D5.S3.Quantum.Matrix.CayleyResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

abbrev Mat (n : ℕ) := _root_.Matrix (Fin n) (Fin n) ℂ
abbrev Params := Σ n : ℕ, Σ _s : ℝ, Mat n
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Mat p.1) (fun p => Mat p.1)

def actual : Realization signature :=
  realize signature (fun _ p V => resolvent p.2.1 V - resolvent p.2.1 p.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p V => resolvent p.2.1 V - resolvent p.2.1 p.2.2 + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (s : ℝ), 2 ≤ s → ∀ U V : Mat n,
    (1+U).PosDef → (1-U).PosDef → (1-V).PosDef → U ≤ V →
    (∃ Z : Mat n, R.readout () ⟨n,s,U⟩ V = resolvent s U * Z * resolvent s U ∧
      V-U ≤ Z ∧ Z ≤ (3 : ℝ) • (V-U)) ∧
    (∃ Z : Mat n, R.readout () ⟨n,s,U⟩ V = resolvent s V * Z * resolvent s V ∧
      (1/3 : ℝ) • (V-U) ≤ Z ∧ Z ≤ V-U)

abbrev sourceScope := type_of% (@endpoint_resolvent_factors)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (1 + (0 : Mat 1)).PosDef := by simpa using _root_.Matrix.PosDef.one (n := Fin 1) (R := ℂ)
  have hm : (1 - (0 : Mat 1)).PosDef := by simpa using _root_.Matrix.PosDef.one (n := Fin 1) (R := ℂ)
  obtain ⟨⟨Z,hZ,h0,h1⟩,_⟩ := h (n := 1) 2 (by norm_num) 0 0 hp hm hm le_rfl
  have hz : Z = 0 := le_antisymm (by simpa using h1) (by simpa using h0)
  rw [hz] at hZ
  have he : (1 : Mat 1) = 0 := by simpa [rejected, realize] using hZ
  exact one_ne_zero he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,0,0⟩, 0, -1, ?_⟩
  intro h
  have he := congrArg (fun X : Mat 1 => X 0 0) h
  norm_num [actual, realize, _root_.D5.S3.Quantum.Matrix.CayleyResolvent.resolvent,
    _root_.Matrix.one_apply] at he

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_resolvent_factors, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CayleyResolvent.endpoint_resolvent_factors)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p V => resolvent p.2.1 V - resolvent p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CayleyResolvent
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Cayley

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun n => Mat n)

def actual : Realization signature :=
  realize signature (fun _ _ A => cayley A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A : Mat n), A.PosDef →
    (1+R.readout () n A).PosDef ∧ (1-R.readout () n A).PosDef ∧
      ∀ B : Mat n, B.PosDef → A ≤ B → R.readout () n A ≤ R.readout () n B

abbrev sourceScope := type_of% (@cayley_transport)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (n := 1) 1 _root_.Matrix.PosDef.one).2.1
  have hz : (0 : Mat 1).PosDef := by simpa [rejected, realize] using hh
  exact not_isUnit_zero hz.isUnit

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, -1, ?_⟩
  intro h
  have he := congrArg (fun X : Mat 1 => X 0 0) h
  norm_num [actual, realize, cayley, _root_.Matrix.one_apply] at he

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cayley_transport, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CayleyResolvent.cayley_transport)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.Cayley.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.Cayley.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => cayley A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CayleyResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Cayley

namespace Rational

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _n : ℕ, ℝ)
    (fun p => Mat p.1) (fun p => Mat p.1)

def actual : Realization signature :=
  realize signature (fun _ p A => resolvent p.2 (cayley A)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p A => resolvent p.2 (cayley A) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (s : ℝ), 2 ≤ s → ∀ A : Mat n, A.PosDef →
    R.readout () ⟨n,s⟩ A = (A+1) * ((s-1) • A + (s+1) • (1 : Mat n))⁻¹

abbrev sourceScope := type_of% (@cayley_resolvent)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 1) 2 (by norm_num) 1 _root_.Matrix.PosDef.one
  change resolvent 2 (cayley (1 : Mat 1)) + 1 = _ at he
  rw [cayley_resolvent 2 (by norm_num) 1 _root_.Matrix.PosDef.one] at he
  have hz : (1 : Mat 1) = 0 := add_eq_left.mp he
  have hc := congrArg (fun X : Mat 1 => X 0 0) hz
  norm_num [_root_.Matrix.one_apply] at hc

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,0⟩, 0, -1, ?_⟩
  intro h
  have hz : cayley (0 : Mat 1) = -1 := by
    simp only [cayley, zero_add, inv_one]
    module
  have hn : cayley (-1 : Mat 1) = 1 := by simp [cayley]
  have he := congrArg (fun X : Mat 1 => X 0 0) h
  norm_num [actual, realize, hz, hn,
    _root_.D5.S3.Quantum.Matrix.CayleyResolvent.resolvent, _root_.Matrix.one_apply] at he

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cayley_resolvent, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CayleyResolvent.cayley_resolvent)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.Rational.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.Rational.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p A => resolvent p.2 (cayley A)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CayleyResolvent
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Rational
namespace InverseAntitone
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun n => Mat n → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {P Q : Mat n}, P.PosDef → Q.PosDef → P ≤ Q →
    R.readout () n Q⁻¹ P⁻¹
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (P := 1) (Q := 1) _root_.Matrix.PosDef.one
    _root_.Matrix.PosDef.one le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  change (fun y : Mat 1 => (0 : Mat 1) ≤ y) = (fun y : Mat 1 => (1 : Mat 1) ≤ y) at he
  have h10 : (1 : Mat 1) ≤ 0 := by rw [← congrFun he 0]
  have hd := (_root_.Matrix.le_iff.mp h10).diag_nonneg (i := 0)
  norm_num at hd
def family : Registration arena (type_of% (@inverse_antitone)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_antitone, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@inverse_antitone) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.CayleyResolvent.inverse_antitone.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CayleyResolvent.InverseAntitone.family
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
    owner := `D5.S3.Quantum.Matrix.CayleyResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end InverseAntitone
end
end Reg.D5.S3.Quantum.Matrix.CayleyResolvent
