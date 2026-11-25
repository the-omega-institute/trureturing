import D5.S3.TotalVariation.ParityLogModulus
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound audit for the logarithmic parity modulus. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.ParityLogStability
open _root_.D5.S3.TotalVariation.ParityLogModulus
open _root_.D5.S3.TotalVariation.Pinsker (totalVariation)

namespace Reg.D5.S3.TotalVariation.ParityLogModulus

noncomputable section

universe u

open scoped BigOperators

abbrev signature : Signature where
  Params := Type u
  State A := A → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := A → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ p x => 2 * p x) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [AddCommGroup A] [Fintype A]
    (_two : ∀ x : A, x + x = 0) (_hcard : 1 < Fintype.card A)
    (p q : A → ℝ) (_hmass : ∑ x, p x = ∑ x, q x)
    (a : A) (e : ℝ) (_he : 0 < e)
    (_hp : ∀ ψ, e ≤ |moment p ψ|) (_hq : ∀ ψ, e ≤ |moment q ψ|),
    let beta : ℝ := ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ)
    |logCoefficient a (R.readout () A p) - logCoefficient a q| ≤
      2 * beta * Real.log (1 + totalVariation p q / (beta * e))

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  classical
  let A := ULift.{u} (ZMod 2)
  have hcard : Fintype.card A = 2 := by simp [A, ZMod.card]
  have hn : 1 < Fintype.card A := by rw [hcard]; norm_num
  have htwo (x : A) : x + x = 0 := by
    apply ULift.down_injective
    change x.down + x.down = 0
    have ht : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, ht, zero_mul]
  let pointMass (r : ℝ) (x : A) := if x = 0 then r else 0
  have hmoment (r : ℝ) (ψ : AddChar A ℂ) : moment (pointMass r) ψ = r := by
    unfold moment
    rw [Finset.sum_eq_single (0 : A)]
    · simp [pointMass, sign]
    · intro x _ hx
      simp [pointMass, hx]
    · simp
  have hfloor (ψ : AddChar A ℂ) : (1 : ℝ) ≤ |moment (pointMass 1) ψ| := by
    simp [hmoment]
  have hcoeff (r : ℝ) : logCoefficient (0 : A) (pointMass r) = -2 * Real.log |r| := by
    simp [logCoefficient, hmoment, sign, AddChar.card_eq, hcard]
  have hb := h (A := A) htwo hn (pointMass 1) (pointMass 1) rfl 0 1
    (by norm_num) hfloor hfloor
  have hscale : rejected.readout () A (pointMass 1) = pointMass 2 := by
    funext x
    by_cases hx : x = 0 <;> norm_num [rejected, realize, pointMass, hx]
  change |logCoefficient (0 : A) (rejected.readout () A (pointMass 1)) -
    logCoefficient 0 (pointMass 1)| ≤ _ at hb
  rw [hscale, hcoeff, hcoeff] at hb
  norm_num [totalVariation, hcard, Real.log_one] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_pos hlog] at hb
  linarith

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (ULift.up ())
  norm_num [actual, realize] at hh

def sourceRegistration : Registration arena.{u} (type_of% @log_parity_coefficient_modulus.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_parity_coefficient_modulus, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_parity_coefficient_modulus.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.ParityLogModulus.unit
  realizationName := `Reg.D5.S3.TotalVariation.ParityLogModulus.sourceRegistration
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
    owner := `D5.S3.TotalVariation.ParityLogModulus
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.ParityLogModulus
