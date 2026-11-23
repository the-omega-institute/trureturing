import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCompletion
import Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData
import Reg.D5.S3.CharacterSums.DirichletCompletion.Bounds
import Reg.Support.SingleDependentReadout
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! Typed observations at the original mathematical statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Complex Filter
open scoped Topology
open _root_.D5.S3.CharacterSums.DirichletCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.CharacterSums.DirichletCompletion

private theorem nonprincipal_example : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  refine ⟨χ, ?_⟩
  rintro rfl
  exact hχ (MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))

private theorem primitive_example : ∃ q : ℕ, q ≠ 0 ∧
    ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := nonprincipal_example
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  refine ⟨χ.conductor, χ.conductor_ne_zero, χ.primitiveCharacter,
    χ.primitiveCharacter_isPrimitive, ?_⟩
  intro he
  have hc := χ.primitiveCharacter_isPrimitive
  change χ.primitiveCharacter.conductor = χ.conductor at hc
  rw [he, DirichletCharacter.conductor_one] at hc
  exact hχ ((χ.eq_one_iff_conductor_eq_one).mpr hc.symm)

namespace Entire
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun q => DirichletCharacter ℂ q) (fun q => DirichletCharacter ℂ q → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => True) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
    M.readout () q χ 1 → Differentiable ℂ (completion χ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 : DirichletCharacter ℂ 1) True.intro
  have he : completion (1 : DirichletCharacter ℂ 1) = completedRiemannZeta := by
    funext z
    simp [completion, DirichletCharacter.completedLFunction_modOne_eq]
  rw [he] at hh
  have ht : Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s)
      (𝓝[≠] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => (s - 1) * completedRiemannZeta s) 1 :=
      (continuousAt_id.sub continuousAt_const).mul (hh 1).continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hn := tendsto_nhds_unique ht completedRiemannZeta_residue_one
  norm_num at hn
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨χ, hn⟩ := nonprincipal_example
  refine ⟨3, χ, 1, ?_⟩
  intro h
  have hh := congrFun h χ
  simpa [actual, realize, Ne.symm hn] using hh
def family : Registration arena (type_of% @differentiable_completion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @differentiable_completion,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@differentiable_completion) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.differentiable_completion
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Entire.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Entire

namespace Equation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x * y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (s : ℂ),
    completion χ (1 - s) = M.readout () () χ.rootNumber (completion χ⁻¹ s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (χ := (1 : DirichletCharacter ℂ 1))
    DirichletCharacter.isPrimitive_one_level_one (-1)
  have hn := completion_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ 1)
    (s := 2) (.inr (.inl (by norm_num))) (by norm_num)
  apply hn
  simpa [rejected, realize, map_ofNat, show (1 : ℂ) + 1 = 2 by norm_num] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 1
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_one_sub) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_one_sub,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_one_sub) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_one_sub
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Equation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x * y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Equation

namespace Right
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M :=
    ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hχs : χ ≠ 1 ∨ s ≠ 1 ∨ q = 1) (hs : 1 ≤ s.re),
    M.readout () () (completion χ s) 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using h (1 : DirichletCharacter ℂ 1)
    (s := 2) (.inr (.inl (by norm_num))) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_ne_zero_of_one_le_re) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_ne_zero_of_one_le_re,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_ne_zero_of_one_le_re) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_ne_zero_of_one_le_re
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Right.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Right

namespace Root
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M :=
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive),
      M.readout () () χ.rootNumber 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using
    h (χ := (1 : DirichletCharacter ℂ 1)) DirichletCharacter.isPrimitive_one_level_one
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @rootNumber_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @rootNumber_ne_zero,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rootNumber_ne_zero) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.rootNumber_ne_zero
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Root.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e))
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
end Root

namespace Left
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M :=
    ∀ {q : ℕ} [NeZero q]
      {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0),
    M.readout () () (completion χ s) 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  simpa [rejected, realize] using h hp (s := 0) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_ne_zero_of_re_le_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_ne_zero_of_re_le_zero,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_ne_zero_of_re_le_zero) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_ne_zero_of_re_le_zero
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Left

namespace Conjugation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ x => conj x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    completion χ⁻¹ (conj s) = M.readout () () (completion χ s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hn⟩ := nonprincipal_example
  have hh := h χ 2
  have hni : χ⁻¹ ≠ 1 := inv_ne_one.mpr hn
  have hz := completion_ne_zero_of_one_le_re χ⁻¹ (s := 2) (.inl hni) (by norm_num)
  apply hz
  simpa [rejected, realize, map_ofNat, show (1 : ℂ) + 1 = 2 by norm_num] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @completion_inv_conj) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_inv_conj,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_inv_conj) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_inv_conj
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Conjugation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => conj x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Conjugation

namespace RootNorm
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M :=
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive),
      M.readout () () ‖χ.rootNumber‖ 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using
    h (χ := (1 : DirichletCharacter ℂ 1)) DirichletCharacter.isPrimitive_one_level_one
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @norm_rootNumber) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @norm_rootNumber,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_rootNumber) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.norm_rootNumber
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.RootNorm.family
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
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RootNorm

namespace Explicit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M :=
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ),
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * (1 + ‖s‖) *
      M.readout () () (Real.log (q : ℝ) / 2 * (1 + ‖s‖) +
        ((‖s‖ + 4) / 2) * Real.log ((‖s‖ + 4) / 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  have hh := h hp hn 0
  have hg : 0 < gammaConstant := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ht : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  norm_num only [norm_zero, add_zero, mul_one, rejected, realize] at hh
  have hh0 := norm_nonneg (completion χ 0)
  nlinarith [mul_pos hg ht]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)
def family : Registration arena (type_of% @completion_growth_explicit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_growth_explicit,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_growth_explicit) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_growth_explicit
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Explicit.family
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
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Explicit

namespace Logarithmic
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M :=
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ),
    ‖completion χ s‖ < M.readout () ()
      (growthConstant q * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  have hh := h hp hn 0
  change ‖completion χ 0‖ < -1 at hh
  linarith [norm_nonneg (completion χ 0)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)
def family : Registration arena (type_of% @completion_growth_log) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_growth_log,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_growth_log) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_growth_log
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.Logarithmic.family
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
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Logarithmic

end Reg.D5.S3.CharacterSums.DirichletCompletion
