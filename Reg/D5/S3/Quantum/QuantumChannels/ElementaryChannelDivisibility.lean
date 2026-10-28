import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
import Reg.Support.DependentFamily

/-! Source-bound audit of conjugation of a rank-one operator. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility

open _root_.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_1

namespace KetbraStar

abbrev signature : Signature where
  Params := Σ n : Type u_1, n → ℂ
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ p w => (ketbra p.2 w)ᴴ) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law r := ∀ {n : Type u_1} [Fintype n] [DecidableEq n] (v w : n → ℂ),
    r.readout () ⟨n, v⟩ w = ketbra w v

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have hh := @h (ULift.{u_1} Unit) inferInstance inferInstance
    (fun _ => 1) (fun _ => 1)
  have he := congrArg (fun M => M (ULift.up ()) (ULift.up ())) hh
  simp [rejected, realize, ketbra, Matrix.vecMulVec_apply] at he

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Unit, fun _ => 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrArg (fun M => M (ULift.up ()) (ULift.up ())) h
  simp [actual, realize, ketbra, Matrix.vecMulVec_apply] at he

def source_registration : Registration arena.{u_1} (type_of% (@ketbra_star.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ketbra_star, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ketbra_star.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KetbraStar.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KetbraStar.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end KetbraStar

namespace FactorOfKernel

abbrev signature.{u_1} : Signature where
  Params := Σ n : Type u_1, Matrix n n ℂ × Matrix n n ℂ
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ p C => C * p.2.1) (fun e => nomatch e)

def rejected.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena.{u_1} : Arena where
  signature := signature.{u_1}
  Law R := ∀ {n : Type u_1} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ),
    (∀ v, A *ᵥ v = 0 → B *ᵥ v = 0) →
      ∃ C : Matrix n n ℂ, B = R.readout () ⟨n, A, B⟩ C

theorem rejected_law.{u_1} : ¬ arena.{u_1}.Law rejected := by
  intro h
  have hh := @h (ULift.{u_1} Unit) inferInstance inferInstance
    (1 : Matrix (ULift.{u_1} Unit) (ULift.{u_1} Unit) ℂ)
    1 (by intro v hv; exact hv)
  obtain ⟨C, hC⟩ := hh
  have he := congrArg
    (fun M : Matrix (ULift.{u_1} Unit) (ULift.{u_1} Unit) ℂ =>
      M (ULift.up ()) (ULift.up ())) hC
  simp [rejected, realize] at he

theorem dependence.{u_1} : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Unit, 1, 1⟩, 0, 1, ?_⟩
  intro he
  have he' := congrArg
    (fun M : Matrix (ULift.{u_1} Unit) (ULift.{u_1} Unit) ℂ =>
      M (ULift.up ()) (ULift.up ())) he
  simp [actual, realize] at he'

def source_registration.{u_1} :
    Registration arena.{u_1} (type_of% (@factor_of_kernel.{u_1})) where
  actual := actual
  bridge := by rfl
  variation := ⟨@factor_of_kernel.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration_factor_of_kernel.{u_1} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.factor_of_kernel.{u_1})
      (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.FactorOfKernel.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.FactorOfKernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p C => C * p.2.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end FactorOfKernel

namespace KernelOfSubPsd

abbrev signature.{u_1} : Signature where
  Params := Σ n : Type u_1, Matrix n n ℂ × Matrix n n ℂ
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ p v => p.2.1 *ᵥ v = 0) (fun e => nomatch e)

def rejected.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena.{u_1} : Arena where
  signature := signature.{u_1}
  Law R := ∀ {n : Type u_1} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hB : B.PosSemidef) (t : ℝ) (ht : 0 < t)
    (hAB : (A - t • B).PosSemidef),
    ∀ v, R.readout () ⟨n, A, B⟩ v → B *ᵥ v = 0

theorem rejected_law.{u_1} : ¬ arena.{u_1}.Law rejected := by
  intro h
  have hh := @h (ULift.{u_1} Unit) inferInstance inferInstance
    (1 : Matrix (ULift.{u_1} Unit) (ULift.{u_1} Unit) ℂ)
    1 Matrix.PosSemidef.one 1 (by norm_num) (by simp)
  have hv := hh (fun _ => (1 : ℂ)) trivial
  have he := congrArg (fun z : ℂ => z) hv
  simpa [Matrix.mulVec, dotProduct] using he

theorem dependence.{u_1} : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Unit, 1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have he' := congrArg (fun P : Prop => P) he
  simp [actual, realize, Matrix.mulVec, dotProduct] at he'

def source_registration.{u_1} :
    Registration arena.{u_1} (type_of% (@kernel_of_sub_psd.{u_1})) where
  actual := actual
  bridge := by rfl
  variation := ⟨@kernel_of_sub_psd.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration_kernel_of_sub_psd.{u_1} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.kernel_of_sub_psd.{u_1})
      (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KernelOfSubPsd.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility.KernelOfSubPsd.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => p.2.1 *ᵥ v = 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end KernelOfSubPsd
end
end Reg.D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
