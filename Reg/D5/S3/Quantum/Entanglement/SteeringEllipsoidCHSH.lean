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
