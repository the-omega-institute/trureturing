import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.LowRankPartialTrace

/-! Source-bound squared Frobenius mass observations. -/

namespace Reg.D5.S3.Quantum.Information.LowRankPartialTrace

open Matrix LeanInformationAudit
open scoped BigOperators Matrix Matrix.Norms.Frobenius
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Quantum.Information.LowRankPartialTrace
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

noncomputable def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ x => x ^ 2) (fun a => nomatch a)

noncomputable def positive : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 1) (fun a => nomatch a)

noncomputable def negative : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => -1) (fun a => nomatch a)

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℝ) ^ (2 : ℕ) ≠ 1 ^ (2 : ℕ)
  norm_num

universe u v w l

def rankArena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (K : Matrix (A × B) (A × B) ℂ),
    R.readout () () ‖partialTraceLeft K‖ ≤ (K.rank : ℝ) * ‖K‖ ^ 2

private theorem rank_positive_fails : ¬ (rankArena.{u,v}).Law positive := by
  intro h
  have h0 := h (0 : Matrix (ULift.{u} Unit × ULift.{v} Unit) _ ℂ)
  change (1 : ℝ) ≤
    ((0 : Matrix (ULift.{u} Unit × ULift.{v} Unit) _ ℂ).rank : ℝ) * ‖(0 : Matrix
      (ULift.{u} Unit × ULift.{v} Unit) (ULift.{u} Unit × ULift.{v} Unit) ℂ)‖ ^ 2 at h0
  norm_num [Matrix.rank_zero] at h0

noncomputable def rankFamily :
    DependentFamily.Registration rankArena.{u,v}
      (type_of% (@frobenius_sq_partialTraceLeft_le_rank_mul.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨frobenius_sq_partialTraceLeft_le_rank_mul, positive, rank_positive_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rank_positive_fails
  dependence := dependence

noncomputable def rankRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@frobenius_sq_partialTraceLeft_le_rank_mul.{u,v}) (DependentFamily.Realization signature)
      Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Quantum.Information.LowRankPartialTrace.frobenius_sq_partialTraceLeft_le_rank_mul
    "__information_unit"
  realizationName := `Reg.D5.S3.Quantum.Information.LowRankPartialTrace.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena.{u,v}⟩
  objectArena := .source ⟨rankArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena.{u,v} ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ x => x ^ 2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.LowRankPartialTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def massArena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {C : Type w} [Fintype C] [Nonempty A] [Nonempty B]
    {L : Type l} [Fintype L] (_h : Fintype.card A = Fintype.card B)
    (K : L → Matrix ((A × B) × C) ((A × B) × C) ℂ)
    (_hK : ∀ i, (K i).rank ≤ Fintype.card A),
    (∑ i, (‖expectA (K i)‖ ^ 2 + ‖expectB (K i)‖ ^ 2)) ≤
      (1 + (Fintype.card A : ℝ)⁻¹) * ∑ i, R.readout () () ‖K i‖

private theorem mass_negative_fails : ¬ (massArena.{u,v,w,l}).Law negative := by
  intro h
  let K : ULift.{l} Unit → Matrix
      ((ULift.{u} Unit × ULift.{v} Unit) × ULift.{w} Unit)
      ((ULift.{u} Unit × ULift.{v} Unit) × ULift.{w} Unit) ℂ := fun _ => 0
  have h0 := h (by simp) K (by simp [K])
  norm_num [K, negative, DependentFamily.realize] at h0

noncomputable def massFamily :
    DependentFamily.Registration massArena.{u,v,w,l}
      (type_of% (@two_site_mass_sum_le.{u,v,w,l})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_site_mass_sum_le, negative, mass_negative_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ mass_negative_fails
  dependence := dependence

noncomputable def massRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@two_site_mass_sum_le.{u,v,w,l}) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Information.LowRankPartialTrace.two_site_mass_sum_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.LowRankPartialTrace.massFamily
  realizationSource := none
  generated := false
  arena := .source ⟨massArena.{u,v,w,l}⟩
  objectArena := .source ⟨massArena.{u,v,w,l}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source massArena.{u,v,w,l} ⟨massFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ x => x ^ 2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.LowRankPartialTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def encoderArena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {C : Type w} [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty B] (_h : Fintype.card A = Fintype.card B),
    let V : B × C → Matrix A ((A × B) × C) ℂ := basisEncoder
    let K := fun q => (V q)ᴴ * V q
    (∀ q, V q * (V q)ᴴ = 1) ∧ (∑ q, K q) = 1 ∧
      (∀ q, (K q).rank = Fintype.card A) ∧
      (∀ q, R.readout () () ‖K q‖ = (Fintype.card A : ℝ) ∧ expectA (K q) = K q ∧
        ‖expectB (K q)‖ ^ 2 = 1) ∧
      (∑ q, (‖expectA (K q)‖ ^ 2 + ‖expectB (K q)‖ ^ 2)) =
        (1 + (Fintype.card A : ℝ)⁻¹) * ∑ q, ‖K q‖ ^ 2

private theorem encoder_negative_fails : ¬ (encoderArena.{u,v,w}).Law negative := by
  intro h
  have h0 := @h (ULift.{u} Unit) (ULift.{v} Unit) _ _ _ _ (ULift.{w} Unit) _ _ _ _
    (by simp)
  have hm := (h0.2.2.2.1 (default, default)).1
  norm_num [negative, DependentFamily.realize] at hm

noncomputable def encoderFamily :
    DependentFamily.Registration encoderArena.{u,v,w}
      (type_of% (@basis_encoder_attains.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨basis_encoder_attains, negative, encoder_negative_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ encoder_negative_fails
  dependence := dependence

noncomputable def encoderRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@basis_encoder_attains.{u,v,w}) (DependentFamily.Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Information.LowRankPartialTrace.basis_encoder_attains.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.LowRankPartialTrace.encoderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨encoderArena.{u,v,w}⟩
  objectArena := .source ⟨encoderArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source encoderArena.{u,v,w} ⟨encoderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ x => x ^ 2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.LowRankPartialTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Information.LowRankPartialTrace
