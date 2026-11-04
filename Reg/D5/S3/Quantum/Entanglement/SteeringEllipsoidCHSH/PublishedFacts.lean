import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
import Reg.Support.SingleDependentReadout

/-! Registrations for steering-ellipsoid identities and bounds. -/

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
  readout := some
    (realize signature (fun _ t s => vlen (centre (tightState t s))) (fun e => nomatch e))
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

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BellTrace
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
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : TwoQubit, Σ _ : Fin 3 → ℝ, Σ _ : Fin 3 → ℝ, Fin 3 → ℝ)
    (fun _ => Fin 3 → ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p b' =>
    trace (Sigma.fst p *
      bell (Sigma.fst (Sigma.snd p)) (Sigma.fst (Sigma.snd (Sigma.snd p)))
        (Sigma.snd (Sigma.snd (Sigma.snd p))) b')) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (_hρ : ρ.IsHermitian) (a a' b b' : Fin 3 → ℝ),
    R.readout () ⟨ρ, ⟨a, ⟨a', b⟩⟩⟩ b' =
      ((a ⬝ᵥ (corr ρ *ᵥ (b + b')) + a' ⬝ᵥ (corr ρ *ᵥ (b - b')) : ℝ) : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 (by simp) 0 0 0 0
  change (1 : ℂ) = _ at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨tightState 0 0, ⟨![0, 0, 1], ⟨0, 0⟩⟩⟩, 0, ![0, 0, 1], ?_⟩
  change trace (tightState 0 0 * bell ![0, 0, 1] 0 0 0) ≠
    trace (tightState 0 0 * bell ![0, 0, 1] 0 0 ![0, 0, 1])
  rw [bell_trace_real_expansion _ (tight_psd 0 0 (by norm_num) (by norm_num)).isHermitian,
    bell_trace_real_expansion _ (tight_psd 0 0 (by norm_num) (by norm_num)).isHermitian,
    (tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).2.2.2]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, diagonal]

def source_registration : Registration arena (type_of% @bell_trace_real_expansion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bell_trace_real_expansion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bell_trace_real_expansion) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BellTrace.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BellTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b' =>
    trace (Sigma.fst p *
      bell (Sigma.fst (Sigma.snd p)) (Sigma.fst (Sigma.snd (Sigma.snd p)))
        (Sigma.snd (Sigma.snd (Sigma.snd p))) b')) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.BellTrace

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.FlipPurity
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

open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli_one pauli_two)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature TwoQubit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ ρ n => (trace (ρ * flipped ρ n)).re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (_hρ : ρ.IsHermitian) (_htr : trace ρ = 1)
    (n : Fin 3 → ℝ) (_hn : vlen n = 1),
    2 * R.readout () ρ n + (∑ i, ∑ j, corr ρ i j ^ 2) -
      vlen ((corr ρ) *ᵥ n) ^ 2 + (blochB ρ ⬝ᵥ n) ^ 2 = 1 + 2 * delta ρ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hpρ := tight_psd 0 0 (by norm_num) (by norm_num)
  have htr := (tight_readouts 0 0 (by norm_num) (by norm_num) (by norm_num)).1
  have hn : vlen (![0, 0, 1] : Fin 3 → ℝ) = 1 := by norm_num [vlen_e3]
  have ht := flip_purity_identity (tightState 0 0) hpρ.isHermitian htr ![0, 0, 1] hn
  have hb := h (tightState 0 0) hpρ.isHermitian htr ![0, 0, 1] hn
  change 2 * (-1 : ℝ) + _ - _ + _ = _ at hb
  have hpf : (flipped (tightState 0 0) ![0, 0, 1]).PosSemidef :=
    hpρ.transpose.mul_mul_conjTranspose_same _
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef hpρ hpf
  change 0 ≤ (trace (tightState 0 0 * flipped (tightState 0 0) ![0, 0, 1])).re at hp
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, ![0, 0, 1], ?_⟩
  change (trace ((1 : TwoQubit) * flipped 1 (0 : Fin 3 → ℝ))).re ≠
    (trace ((1 : TwoQubit) * flipped 1 ![0, 0, 1])).re
  norm_num [flipped, flipMatrix, spin, sigma_succ, Fin.sum_univ_three,
    pauli_one, pauli_two, trace, diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, kronecker_apply,
    conjTranspose_apply, transpose_apply]

def source_registration : Registration arena (type_of% @flip_purity_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨flip_purity_identity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@flip_purity_identity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.FlipPurity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.FlipPurity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ ρ n => (trace (ρ * flipped ρ n)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH.FlipPurity
