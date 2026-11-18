import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Matrix.BKMProjectionRigidity

/-! Source registrations for the ambient power integral and resolvent inverse. -/

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Divergence.LogDerivTrace (logDeriv)
open _root_.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
open _root_.D5.S3.Quantum.Matrix.BKMProjectionRigidity (omega_of_commute)
open _root_.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction (omega)
open scoped ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse

universe u
private abbrev Mat (n : Type u) := Matrix n n ℂ
private abbrev Index := ULift.{u} Unit

private theorem power_one : omega (1 : Mat Index.{u}) 1 = 1 := by
  rw [omega_of_commute _ _ Matrix.PosDef.one (Commute.one_right _), mul_one]

private theorem resolvent_one : logDeriv (1 : Mat Index.{u}) 1 = 1 := by
  calc
    logDeriv (1 : Mat Index.{u}) 1 =
        logDeriv (1 : Mat Index.{u}) (omega (1 : Mat Index.{u}) 1) :=
      congrArg (logDeriv (1 : Mat Index.{u})) power_one.symm
    _ = 1 := (inverse_identities (1 : Mat Index.{u}) Matrix.PosDef.one).1 1

namespace Ambient

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Σ _ : Fintype n, Σ _ : DecidableEq n, Mat n)
    (fun p => Mat p.1) (fun p => Mat p.1)

def power : Realization signature.{u} :=
  realize signature (fun _ p X => by
    letI := p.2.1
    letI := p.2.2.1
    exact omega p.2.2.2 X) (fun e => nomatch e)

def resolvent : Realization signature.{u} :=
  realize signature (fun _ p X => by
    letI := p.2.1
    letI := p.2.2.1
    exact logDeriv p.2.2.2 X) (fun e => nomatch e)

def zero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem power_dep : ObservationalDependence signature.{u} power := by
  intro _
  refine ⟨⟨Index, inferInstance, inferInstance, 1⟩, 0, 1, ?_⟩
  exact fun h => zero_ne_one ((inverse_identities (1 : Mat Index) Matrix.PosDef.one).1.injective h)

private theorem resolvent_dep : ObservationalDependence signature.{u} resolvent := by
  intro _
  refine ⟨⟨Index, inferInstance, inferInstance, 1⟩, 0, 1, ?_⟩
  exact fun h => zero_ne_one ((inverse_identities (1 : Mat Index) Matrix.PosDef.one).2.injective h)

namespace Identities

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (D : Mat n) (_hD : D.PosDef),
    Function.LeftInverse (R.readout () ⟨n, inferInstance, inferInstance, D⟩) (omega D) ∧
      Function.RightInverse (logDeriv D) (omega D)

private theorem zero_fails : ¬ arena.{u}.Law zero := by
  intro h
  have hz := (h (1 : Mat Index.{u}) Matrix.PosDef.one).1 1
  exact zero_ne_one (show (0 : Mat Index.{u}) = 1 from hz)


def family : Registration arena.{u} (type_of% (@inverse_identities.{u})) where
  actual := resolvent
  bridge := Iff.rfl
  variation := ⟨@inverse_identities.{u}, zero, zero_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law resolvent zero zero_fails
  dependence := resolvent_dep

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@inverse_identities.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse.Ambient.Identities.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse.Ambient.Identities.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature resolvent.readout resolvent.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Identities

namespace Forward

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (D : Mat n) (hD : D.PosDef) (X : Mat n),
    omegaEquiv D hD X = R.readout () ⟨n, inferInstance, inferInstance, D⟩ X

private theorem zero_fails : ¬ arena.{u}.Law zero := by
  intro h
  have hz := h (1 : Mat Index.{u}) Matrix.PosDef.one 1
  exact one_ne_zero ((omegaEquiv_apply (1 : Mat Index.{u}) Matrix.PosDef.one 1).symm.trans
    hz |> fun he => power_one.symm.trans he)


def family : Registration arena.{u} (type_of% (@omegaEquiv_apply.{u})) where
  actual := power
  bridge := Iff.rfl
  variation := ⟨@omegaEquiv_apply.{u}, zero, zero_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law power zero zero_fails
  dependence := power_dep

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaEquiv_apply.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse.Ambient.Forward.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse.Ambient.Forward.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature power.readout power.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Forward

namespace Backward

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (D : Mat n) (hD : D.PosDef) (X : Mat n),
    (omegaEquiv D hD).symm X = R.readout () ⟨n, inferInstance, inferInstance, D⟩ X

private theorem zero_fails : ¬ arena.{u}.Law zero := by
  intro h
  have hz := h (1 : Mat Index.{u}) Matrix.PosDef.one 1
  exact one_ne_zero ((omegaEquiv_symm_apply (1 : Mat Index.{u}) Matrix.PosDef.one 1).symm.trans
    hz |> fun he => resolvent_one.symm.trans he)


def family : Registration arena.{u} (type_of% (@omegaEquiv_symm_apply.{u})) where
  actual := resolvent
  bridge := Iff.rfl
  variation := ⟨@omegaEquiv_symm_apply.{u}, zero, zero_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law resolvent zero zero_fails
  dependence := resolvent_dep

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaEquiv_symm_apply.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse.Ambient.Backward.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse.Ambient.Backward.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature resolvent.readout resolvent.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Backward

end Ambient

end Reg.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
