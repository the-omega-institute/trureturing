import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletTrivialZeros
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex
open scoped Classical
open _root_.D5.S3.CharacterSums.DirichletTrivialZeros
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletTrivialZeros

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ → ℂ) (fun _ => ℂ → ℕ∞)

def actual : Realization signature :=
  realize signature (fun _ _ f => analyticOrderAt f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (_h0 : s ≠ 0 ∨ q ≠ 1) (_h1 : s ≠ 1 ∨ χ ≠ 1),
    (χ.LFunction s = 0 ↔ χ.completedLFunction s = 0 ∨
      ∃ n : ℕ, s = trivialPoint χ n) ∧
    V.readout () () χ.LFunction s = analyticOrderAt χ.completedLFunction s +
      if ∃ n : ℕ, s = trivialPoint χ n then 1 else 0

private def sample : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

private theorem sample_ne_one : sample ≠ 1 := by
  intro h
  have hh := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  have hone : (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) = 1 :=
    MulChar.one_apply (by decide)
  have hs : sample (3 : ZMod 4) = (-1 : ℂ) := by
    norm_num [sample, MulChar.ringHomComp_apply, ZMod.χ₄]
  rw [hs, hone] at hh
  norm_num at hh

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h sample (trivialPoint sample 0) (.inr (by decide)) (.inr sample_ne_one)).2
  have ht : ∃ n : ℕ, trivialPoint sample 0 = trivialPoint sample n := ⟨0, rfl⟩
  simp only [ht, if_pos, rejected, realize] at hh
  have hp : (0 : ℕ∞) < analyticOrderAt sample.completedLFunction
      (trivialPoint sample 0) + 1 := by positivity
  exact (ne_of_gt hp) hh.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℂ → ℂ), (1 : ℂ → ℂ), ?_⟩
  intro h
  have hh := congrFun h 0
  change analyticOrderAt (0 : ℂ → ℂ) 0 = analyticOrderAt (1 : ℂ → ℂ) 0 at hh
  rw [analyticOrderAt_zero,
    (show AnalyticAt ℂ (1 : ℂ → ℂ) 0 from analyticAt_const).analyticOrderAt_eq_zero.mpr
      (by norm_num)] at hh
  exact ENat.top_ne_zero hh

def family : Registration arena (type_of% @LFunction_zero_divisor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@LFunction_zero_divisor, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@LFunction_zero_divisor) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrivialZeros.LFunction_zero_divisor "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrivialZeros.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => analyticOrderAt f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrivialZeros
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace gamma_growth_boundsRegistration
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V :=
    (∀ {z : ℂ}, 0 < z.re → V.readout () () (Complex.Gamma z) ≤ Real.Gamma z.re) ∧
    (∀ {u : ℝ}, 1 / 4 ≤ u → Real.Gamma u ≤ Real.Gamma (1 / 4) ∨
      Real.Gamma u < Real.exp ((u + 1) * Real.log (u + 1))) ∧
    (∀ {u : ℝ}, 1 / 4 ≤ u → Real.Gamma u ≤
      max (Real.Gamma (1 / 4)) (Nat.factorial (⌈u⌉₊ - 1) : ℝ))
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 (z := 1) (by norm_num)
  change (2 : ℝ) ≤ Real.Gamma 1 at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @gamma_growth_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gamma_growth_bounds, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gamma_growth_bounds) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrivialZeros.gamma_growth_bounds "__information_unit"
  realizationName :=
    `Reg.D5.S3.CharacterSums.DirichletTrivialZeros.gamma_growth_boundsRegistration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrivialZeros
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end gamma_growth_boundsRegistration

namespace completion_power_growthRegistration
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V :=
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 → ∀ s : ℂ,
    (1 / 2 ≤ s.re ∨ χ.IsPrimitive) →
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * (1 + ‖s‖) *
      Real.exp (Real.log (q : ℝ) / 2 * (1 + ‖s‖) +
        ((‖s‖ + 4) / 2) * Real.log ((‖s‖ + 4) / 2)) ∧
    ‖completion χ s‖ < Real.exp
      (growthConstant q * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) ∧
    ‖completion χ s‖ <
      V.readout () () (3 * growthConstant q * (1 + ‖s‖) ^ (3 / 2 : ℝ))
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h sample_ne_one 2 (Or.inl (by norm_num))
  have hh := hh.2.2
  change ‖completion sample 2‖ < (-1 : ℝ) at hh
  linarith [norm_nonneg (completion sample 2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  simp only [actual, realize]
  exact fun h => (zero_ne_one : (0 : ℝ) ≠ 1) (Real.exp_injective h)
def family : Registration arena (type_of% @completion_power_growth) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completion_power_growth, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_power_growth) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrivialZeros.completion_power_growth "__information_unit"
  realizationName :=
    `Reg.D5.S3.CharacterSums.DirichletTrivialZeros.completion_power_growthRegistration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrivialZeros
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end completion_power_growthRegistration

namespace completion_zero_stripRegistration
open scoped Classical
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ → ℂ)
    (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ z f => f z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V :=
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
    ∀ {ρ : ℂ}, V.readout () ρ (completion χ) = 0 → 0 < ρ.re ∧ ρ.re < 1
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  letI : NeZero sample.conductor := ⟨sample.conductor_ne_zero⟩
  have hh := (h sample.primitiveCharacter_isPrimitive (ρ := 2) rfl).2
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨0, (fun _ => 0), (fun _ => 1), by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @completion_zero_strip) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completion_zero_strip, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_zero_strip) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrivialZeros.completion_zero_strip "__information_unit"
  realizationName :=
    `Reg.D5.S3.CharacterSums.DirichletTrivialZeros.completion_zero_stripRegistration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z f => f z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrivialZeros
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end completion_zero_stripRegistration


private theorem primitive_exists :
    ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ℂ (show (-1 : ZMod 3) ≠ 1 by decide)
  have hne : χ ≠ 1 := by
    intro h
    rw [h] at hχ
    exact hχ (MulChar.one_apply (isUnit_one.neg))
  have hp : χ.IsPrimitive := by
    rcases (show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd
      χ.conductor χ.conductor_dvd_level with h | h
    · exact (hne (χ.eq_one_iff_conductor_eq_one.mpr h)).elim
    · exact h
  exact ⟨χ, hp, hne⟩

namespace VerticalResolvent
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x.re + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (_hχ : χ.IsPrimitive) (_hne : χ ≠ 1) (σ t : ℝ)
    (_hcenter : completion χ ((σ : ℂ) + t * I) ≠ 0),
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * (σ - ρ.1.re) /
        ((σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2))
      (R.readout () () (logDeriv (completion χ) ((σ : ℂ) + t * I)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hχ, hne⟩ := primitive_exists
  have hs : completion χ ((2 : ℂ) + 0 * I) ≠ 0 :=
    by
      apply mul_ne_zero (Complex.exp_ne_zero _)
      intro hz
      apply χ.LFunction_ne_zero_of_one_le_re (s := (2 : ℂ) + 0 * I)
        (.inl hne) (by norm_num)
      rw [χ.LFunction_eq_completed_div_gammaFactor _
        (.inr (fun h => hne (DirichletCharacter.level_one' χ h))), hz, zero_div]
  have hh := (h hχ hne 2 0 hs).unique
    (completion_vertical_resolvent hχ hne 2 0 hs)
  change (logDeriv (completion χ) ((2 : ℂ) + 0 * I)).re + 1 =
    (logDeriv (completion χ) ((2 : ℂ) + 0 * I)).re at hh
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @completion_vertical_resolvent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completion_vertical_resolvent, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_vertical_resolvent) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrivialZeros.completion_vertical_resolvent
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrivialZeros.VerticalResolvent.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrivialZeros
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end VerticalResolvent

namespace CompletionLogDerivative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ → ℂ)
    (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p x => logDeriv x p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p x => logDeriv x p + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (_hs : 0 < s.re) (_hL : χ.LFunction s ≠ 0) (_hpole : s ≠ 1 ∨ χ ≠ 1),
    R.readout () s (completion χ) =
      ((Real.log (q : ℝ) - Real.log Real.pi) / 2 : ℝ) +
      (1 / 2 : ℂ) * Complex.digamma ((s + (if χ.Even then 0 else 1)) / 2) +
      logDeriv χ.LFunction s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hL : sample.LFunction 2 ≠ 0 :=
    sample.LFunction_ne_zero_of_one_le_re (.inl sample_ne_one) (by norm_num)
  have h0 := completion_logDeriv sample (s := 2) (by norm_num) hL (.inr sample_ne_one)
  have h1 := h sample (s := 2) (by norm_num) hL (.inr sample_ne_one)
  change logDeriv (completion sample) 2 + 1 = _ at h1
  rw [← h0] at h1
  have he := congrArg Complex.re h1
  simp only [add_re, one_re] at he
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, (fun _ => 1), id, by norm_num [actual, realize, logDeriv_id]⟩
def family : Registration arena (type_of% @completion_logDeriv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completion_logDeriv, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_logDeriv) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrivialZeros.completion_logDeriv
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrivialZeros.CompletionLogDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => logDeriv x p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrivialZeros
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CompletionLogDerivative

end Reg.D5.S3.CharacterSums.DirichletTrivialZeros
