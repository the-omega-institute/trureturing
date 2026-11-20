import D5.S3.TotalVariation.PositiveParitySpectrum
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Data.ZMod.Basic

/-! Source audit for the realizing law in the positive parity spectrum criterion. -/

open _root_.D5.S3.TotalVariation.GroupedParityBias
open _root_.D5.S3.TotalVariation.PositiveParitySpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.TotalVariation.PositiveParitySpectrum

noncomputable section
open scoped BigOperators

universe u v

abbrev signature : Signature where
  Params := Type u
  State A := A → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := A → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ p => p) (fun a => nomatch a)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [AddCommGroup A] [Fintype A]
      (_two : ∀ x : A, x + x = 0) (p : A → ℝ) (_hnorm : ∑ x, p x = 1)
      (_hpos : ∀ ψ, 0 < moment p ψ),
    (∀ {I : Type v} [Fintype I] (c : I → A) (s : A) (q : I → ℝ),
      (∀ i, |q i| ≤ 1) → law c s q = p → orderedMomentProducts p) ∧
    (orderedMomentProducts p → ∃ q : A → ℝ,
      (∀ a, q a ∈ Set.Ioc (0 : ℝ) 1) ∧ law id 0 q = R.readout () A p)

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} (ZMod 2)
  let p (x : A) : ℝ := if x = 0 then 1 else 0
  have htwo (x : A) : x + x = 0 := by
    apply ULift.down_injective
    change x.down + x.down = 0
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have hpoint (f : A → ℝ) : ∑ x, p x * f x = f 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [p]
    · intro x _ hx
      simp [p, hx]
    · simp
  have hnorm : ∑ x, p x = 1 := by simpa using hpoint (fun _ => 1)
  have hm (ψ : AddChar A ℂ) : moment p ψ = 1 := by
    simpa [moment, sign] using hpoint (sign ψ)
  have hpos (ψ : AddChar A ℂ) : 0 < moment p ψ := hm ψ ▸ zero_lt_one
  have hcond : orderedMomentProducts p := by
    intro a ha
    simp [hm]
  obtain ⟨q, hq, hqeq⟩ := (h htwo p hnorm hpos).2 hcond
  change law id 0 q = (fun _ => 0) at hqeq
  have hzero : moment (law id 0 q) 0 = 1 := by
    rw [moment_factor htwo]
    norm_num [sign]
  rw [hqeq] at hzero
  simp [moment] at hzero

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (ULift.up ())
  norm_num [actual, realize] at hh

def sourceRegistration :
    Registration arena.{u,v} (type_of% @positive_moment_realizability.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_moment_realizability, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro other unequal
        exact (unequal (Subsingleton.elim _ _)).elim
      · funext a
        exact nomatch a
    · intro a
      exact nomatch a
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@positive_moment_realizability.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.PositiveParitySpectrum.unit
  realizationName := `Reg.D5.S3.TotalVariation.PositiveParitySpectrum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.PositiveParitySpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
                "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.PositiveParitySpectrum
