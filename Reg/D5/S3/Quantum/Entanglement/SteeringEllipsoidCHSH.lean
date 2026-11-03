import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen centre)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the centre-dependent function in the universal CHSH upper bound. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => bound t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- The Law retains all density-matrix hypotheses and the complete tightness clause. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ ρ : TwoQubit, ρ.PosSemidef → Matrix.trace ρ = 1 →
      chsh ρ ≤ R.readout () () (vlen (centre ρ))) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ ρ : TwoQubit,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ vlen (centre ρ) = t ∧
        bound t - ε < chsh ρ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hε : 0 < 2 * Real.sqrt 2 - 2 := by linarith
  obtain ⟨ρ, hρ, htrace, _, hchsh⟩ :=
    result.2 0 (by norm_num) (by norm_num) (2 * Real.sqrt 2 - 2) hε
  have hupper : chsh ρ ≤ 2 := h.1 ρ hρ htrace
  have hb : bound 0 = 2 * Real.sqrt 2 := by
    simp only [bound, sub_zero, mul_one,
      max_eq_left (by linarith : (2 : ℝ) ≤ 2 * Real.sqrt 2)]
  rw [hb] at hchsh
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change bound 0 ≠ bound 1
  have hs : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hb : bound 0 = 2 * Real.sqrt 2 := by
    simp only [bound, sub_zero, mul_one,
      max_eq_left (by linarith : (2 : ℝ) ≤ 2 * Real.sqrt 2)]
  have hb' : bound 1 = 2 := by norm_num [bound]
  rw [hb, hb']
  linarith

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => bound t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
      name := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli corr)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker

noncomputable section
namespace PauliKroneckerTrace

/-- Observe the complex trace of the joint Pauli coefficient. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ Z => trace Z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (_hρ : ρ.IsHermitian) (i j : Fin 3),
    R.readout () () (ρ * (pauli i ⊗ₖ pauli j)) = (corr ρ i j : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 (by simp) 0 0
  norm_num [rejected, realize, corr] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change trace (0 : TwoQubit) ≠ trace (1 : TwoQubit)
  norm_num [trace_one]

def source_registration : Registration arena (type_of% @trace_pauli_kronecker_eq_corr) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_pauli_kronecker_eq_corr, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_pauli_kronecker_eq_corr) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.PauliKroneckerTrace.unit
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
      "PauliKroneckerTrace") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z => trace Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PauliKroneckerTrace
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (vlen vlen_e3)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace VectorLengthSquared

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => vlen v ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fin 3 → ℝ,
    R.readout () () v = v ⬝ᵥ v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ![0, 0, 1]
  norm_num [rejected, realize, vlen]
    at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![0, 0, 1], ?_⟩
  change (vlen (0 : Fin 3 → ℝ)) ^ 2 ≠ vlen ![0, 0, 1] ^ 2
  rw [vlen_e3]
  norm_num [vlen]

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.vlen_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.vlen_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.vlen_sq)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.VectorLengthSquared.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.VectorLengthSquared.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => vlen v ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end VectorLengthSquared
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (vlen vlen_e3)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace NormalizedUnit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => vlen v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : Fin 3 → ℝ) (hu : u ≠ 0),
    R.readout () () ((vlen u)⁻¹ • u) = 1 ∧
      vlen u • ((vlen u)⁻¹ • u) = u

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h ![0, 0, 1] (by norm_num)).1
  norm_num [rejected, realize, vlen] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![0, 0, 1], ?_⟩
  change vlen (0 : Fin 3 → ℝ) ≠ vlen ![0, 0, 1]
  rw [vlen_e3]
  norm_num [vlen]

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.normalized_unit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.normalized_unit,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.normalized_unit)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.NormalizedUnit.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.NormalizedUnit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => vlen v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end NormalizedUnit
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH (sigma_succ)
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli pauli_zero pauli_two)
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SigmaSuccessor

/-- Observe the Pauli matrix as its index varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ i => pauli i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  change pauli 0 ≠ pauli 2
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  norm_num [pauli_zero, pauli_two] at he

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 3, sigma i.succ = R.readout () () i

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0
  change sigma (0 : Fin 3).succ = (0 : Matrix (Fin 2) (Fin 2) ℂ) at hz
  rw [sigma_succ, pauli_zero] at hz
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) hz
  norm_num [Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @sigma_succ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sigma_succ, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.sigma_succ)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.SigmaSuccessor.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.SigmaSuccessor
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end SigmaSuccessor
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.UnitDot
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH (unit_dot_le)
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (vlen vlen_e3)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => vlen x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a x : Fin 3 → ℝ) (_ha : vlen a = 1), |a ⬝ᵥ x| ≤ R.readout () () x

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ![0, 0, 1] 0 (by norm_num [vlen_e3])
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![0, 0, 1], ?_⟩
  change vlen (0 : Fin 3 → ℝ) ≠ vlen ![0, 0, 1]
  norm_num [vlen, Fin.sum_univ_succ]

def source_registration : Registration arena (type_of% @unit_dot_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unit_dot_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@unit_dot_le) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.UnitDot.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.UnitDot.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => vlen x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.UnitDot

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BobRadius
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 blochA blochB corr centre pauli)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ρ => vlen (blochB ρ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (_hρ : ρ.PosSemidef) (_htr : trace ρ = 1),
    R.readout () () ρ ≤ 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (tightState 0 0) (tight_psd 0 0 (by norm_num) (by norm_num))
    (tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).1
  change (2 : ℝ) ≤ 1 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, tightState 0 1, ?_⟩
  change vlen (blochB 0) ≠ vlen (blochB (tightState 0 1))
  rw [(tight_readouts 0 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1, vlen_e3]
  norm_num [blochB, vlen]

def source_registration : Registration arena (type_of% @bob_radius_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bob_radius_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bob_radius_le) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BobRadius.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BobRadius.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => vlen (blochB ρ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BobRadius

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.DeltaCentre
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 blochA blochB corr centre pauli)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ρ => delta ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (_hρ : ρ.PosSemidef) (_htr : trace ρ = 1),
    R.readout () () ρ ≤ (1 - vlen (blochB ρ) ^ 2) * (1 / 2 - vlen (centre ρ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (tightState 0 0) (tight_psd 0 0 (by norm_num) (by norm_num))
    (tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).1
  change (1 : ℝ) ≤
    (1 - vlen (blochB (tightState 0 0)) ^ 2) * (1 / 2 - vlen (centre (tightState 0 0))) at he
  rw [tight_centre 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).2.2.1, vlen_e3] at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change delta (0 : TwoQubit) ≠ delta 1
  norm_num [delta, _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    trace, diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

def source_registration : Registration arena (type_of% @delta_le_centre) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨delta_le_centre, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@delta_le_centre) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.DeltaCentre.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.DeltaCentre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => delta ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.DeltaCentre

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightPsd
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 blochA blochB corr centre pauli)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => TwoQubit)

def actual : Realization signature :=
  realize signature (fun _ t s => tightState t s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t s : ℝ) (_ht : 0 ≤ t) (_hs : s ≤ 1), (R.readout () t s).PosSemidef

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 (by norm_num) (by norm_num)
  change (-1 : TwoQubit).PosSemidef at he
  have hd := he.diag_nonneg (i := (0, 0))
  norm_num [Complex.le_def] at hd

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change tightState 0 0 ≠ tightState 0 1
  intro h
  have he := congrArg (fun ρ : TwoQubit => blochB ρ 2) h
  rw [(tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).2.2.1,
    (tight_readouts 0 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1] at he
  norm_num at he

def source_registration : Registration arena (type_of% @tight_psd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tight_psd, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tight_psd) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightPsd.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightPsd.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t s => tightState t s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightPsd

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightReadouts
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 blochA blochB corr centre pauli)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => Fin 3 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ t s => blochB (tightState t s)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ![0, 0, 2]) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t s : ℝ) (_ht₁ : t ≤ 1) (_hs₀ : 0 ≤ s) (_hs₁ : s ≤ 1),
    trace (tightState t s) = 1 ∧
    blochA (tightState t s) = ![0, 0, t + (1 - t) * s] ∧
    R.readout () t s = ![0, 0, s] ∧
    corr (tightState t s) = diagonal
      ![Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s)),
        -(Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s))), 1 - t + t * s]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 0 (by norm_num) (by norm_num) (by norm_num)).2.2.1
  change (![0, 0, 2] : Fin 3 → ℝ) = ![0, 0, 0] at he
  have hh := congrFun he 2
  norm_num at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change blochB (tightState 0 0) ≠ blochB (tightState 0 1)
  rw [(tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).2.2.1,
    (tight_readouts 0 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1]
  intro h
  have he := congrFun h 2
  norm_num at he

def source_registration : Registration arena (type_of% @tight_readouts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tight_readouts, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tight_readouts) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightReadouts.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightReadouts.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t s => blochB (tightState t s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightReadouts

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightCentre
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 blochA blochB corr centre pauli)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ t s => vlen (centre (tightState t s))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t s : ℝ) (_ht₀ : 0 ≤ t) (_ht₁ : t ≤ 1) (_hs₀ : 0 ≤ s) (_hs₁ : s < 1),
    R.readout () t s = t

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (-1 : ℝ) = 0 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change vlen (centre (tightState 0 0)) ≠ vlen (centre (tightState 0 1))
  rw [tight_centre 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have ha := (tight_readouts 0 1 (by norm_num) (by norm_num) (by norm_num)).2.1
  have hb := (tight_readouts 0 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1
  norm_num [centre, hb, ha, vlen_e3]

def source_registration : Registration arena (type_of% @tight_centre) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tight_centre, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tight_centre) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightCentre.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightCentre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t s => vlen (centre (tightState t s))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.TightCentre
