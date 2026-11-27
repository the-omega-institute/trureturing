import D5.S3.CharacterSums.DirichletZeroPowerSums
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The final real-part readout is fixed by the actual complex zero sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex
open _root_.D5.S3.CharacterSums.DirichletZeroPowerSums
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletZeroPowerSums

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => z.re + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
    χ.IsPrimitive → χ ≠ 1 → ∀ (k : ℕ), 1 ≤ k → ∀ t : ℝ,
    HasSum (fun ρ : {z : ℂ // χ.LFunction z = 0} =>
      (analyticOrderNatAt χ.LFunction ρ.1 : ℂ) *
        (2 + t * I - ρ.1)⁻¹ ^ (k + 1)) (-(∑' n, momentTerm χ k t n)) ∧
    Summable (fun ρ : {z : ℂ // χ.LFunction z = 0} =>
      ‖(analyticOrderNatAt χ.LFunction ρ.1 : ℂ) *
        (2 + t * I - ρ.1)⁻¹ ^ (k + 1)‖) ∧
    moment χ k t = V.readout () () (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℂ) *
        (2 + t * I - ρ.1)⁻¹ ^ (k + 1))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  have hne : χ ≠ 1 := by
    intro he
    subst χ
    exact hχ (MulChar.one_apply (show IsUnit (-1 : ZMod 3) from isUnit_one.neg))
  have hp : χ.IsPrimitive := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp χ.conductor_dvd_level with hc | hc
    · exact (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc)).elim
    · exact hc
  have hb := (h hp hne 1 (by norm_num) 0).2.2
  have ha := (moment_zero_power_hasSum hp hne 1 (by norm_num) 0).2.2
  change moment χ 1 0 = _ + 1 at hb
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @moment_zero_power_hasSum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_zero_power_hasSum, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_zero_power_hasSum) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletZeroPowerSums.moment_zero_power_hasSum "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletZeroPowerSums.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletZeroPowerSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Truncation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (k X : ℕ) (t : ℝ),
    Summable (momentTerm χ k t) ∧
      (0 < X → ‖(∑' n, momentTerm χ k t n) -
        ∑ n ∈ Finset.range (X + 1), momentTerm χ k t n‖ ≤
          2 ^ (k + 2) * (k + 1) * (X : ℝ) ^ (-1 / 2 : ℝ)) ∧
      (Real.exp (4 * (k + 1 : ℝ)) ≤ (X : ℝ) →
        V.readout () () ((∑' n, momentTerm χ k t n) -
          ∑ n ∈ Finset.range (X + 1), momentTerm χ k t n) ≤ (2 / 3 : ℝ) ^ (k + 1) ∧
        |moment χ k t - finiteMoment χ k X t| ≤ (2 / 3 : ℝ) ^ (k + 1))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hx := h (1 : DirichletCharacter ℂ 1) 0 ⌈Real.exp 4⌉₊ 0
  have hx := (hx.2.2 (by simpa using Nat.le_ceil (Real.exp 4))).1
  change (2 : ℝ) ≤ (2 / 3 : ℝ) ^ (0 + 1) at hx
  norm_num at hx

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @finite_moment_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_moment_error, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_moment_error) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletZeroPowerSums.finite_moment_error "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletZeroPowerSums.Truncation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletZeroPowerSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "body",
        "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Truncation

end Reg.D5.S3.CharacterSums.DirichletZeroPowerSums
