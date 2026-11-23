import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCompletion
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Complex Filter
open scoped Topology
open _root_.D5.S3.CharacterSums.DirichletCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private nonprincipal_example primitive_example from
  Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData
namespace Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds

namespace RightRadius
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    {s : ℂ} {R : ℝ} (hs : 1 / 2 ≤ s.re) (hn : ‖s‖ ≤ R),
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * R *
      M.readout () () (Real.log (q : ℝ) / 2 * R +
        ((R + 3) / 2) * Real.log ((R + 3) / 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hn⟩ := nonprincipal_example
  have hh := h χ hn (s := 2) (R := 2) (by norm_num) (by norm_num)
  have hg : 0 < gammaConstant := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  norm_num [rejected, realize] at hh
  nlinarith [norm_nonneg (completion χ 2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)
def family : Registration arena (type_of% @right_growth_radius) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @right_growth_radius,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_growth_radius) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.right_growth_radius
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds.RightRadius.family
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
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RightRadius


namespace FreeRadius
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (R : ℝ)
    (hside : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) (hn : 1 / 2 ≤ s.re → ‖s‖ ≤ R)
    (href : s.re < 1 / 2 → ‖1 - s‖ ≤ R),
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * R *
      M.readout () () (Real.log (q : ℝ) / 2 * R +
        ((R + 3) / 2) * Real.log ((R + 3) / 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  have hh := h χ hn 2 2 (.inl (by norm_num)) (fun _ => by norm_num)
    (fun h => by norm_num at h)
  have hg : 0 < gammaConstant := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ht : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ‖completion χ 2‖ < gammaConstant * (q.totient : ℝ) * 2 * -1 at hh
  nlinarith [norm_nonneg (completion χ 2), mul_pos hg ht]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)
def family : Registration arena (type_of% @completion_growth_radius) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_growth_radius,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_growth_radius) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_growth_radius
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds.FreeRadius.family
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
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FreeRadius

namespace DirichletLog
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ),
    M.readout () () ‖logDeriv χ.LFunction (2 + t * I)‖
      (Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (1 : DirichletCharacter ℂ 1) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @norm_logDeriv_LFunction_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @norm_logDeriv_LFunction_two,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_logDeriv_LFunction_two) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.norm_logDeriv_LFunction_two
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds.DirichletLog.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DirichletLog

namespace Factorization
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re)
    (hL : χ.LFunction s ≠ 0) (hpole : s ≠ 1 ∨ χ ≠ 1),
    M.readout () () (logDeriv (completion χ) s)
      (((Real.log (q : ℝ) - Real.log Real.pi) / 2 : ℝ) +
        (1 / 2 : ℂ) * Complex.digamma ((s + (if χ.Even then 0 else 1)) / 2) +
        logDeriv χ.LFunction s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hL := (1 : DirichletCharacter ℂ 1).LFunction_ne_zero_of_one_le_re
    (s := 2) (.inr (by norm_num)) (by norm_num)
  exact h (1 : DirichletCharacter ℂ 1) (s := 2) (by norm_num) hL (.inl (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_logDeriv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_logDeriv,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_logDeriv) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_logDeriv
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds.Factorization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Factorization


namespace Center
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
    M.readout () () (2 * (logDeriv (completion χ) 2).re)
      (Real.log (q : ℝ) - Real.log Real.pi + Real.log ((2 + if χ.Even then 0 else 1) / 2 : ℝ) +
        2 * (Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (1 : DirichletCharacter ℂ 1)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_center_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_center_bound,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_center_bound) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_center_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds.Center.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Center

namespace Vertical
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
    M.readout () () (logDeriv (completion χ) (2 + t * I)).re
      ((Real.log (q : ℝ) - Real.log Real.pi + Real.log (|t| + 3)) / 2 +
        (Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3)) ∧
      (χ.IsPrimitive → χ ≠ 1 → 0 ≤ (logDeriv (completion χ) (2 + t * I)).re)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (1 : DirichletCharacter ℂ 1) 0).1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 1
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_vertical_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_vertical_bound,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_vertical_bound) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_vertical_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds.Vertical.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Vertical

end Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds
