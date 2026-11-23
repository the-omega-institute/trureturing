import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCompletion
import Reg.Support.SingleDependentReadout
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Complex Filter
open scoped Topology
open _root_.D5.S3.CharacterSums.DirichletCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData

theorem nonprincipal_example : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  refine ⟨χ, ?_⟩
  rintro rfl
  exact hχ (MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))

theorem primitive_example : ∃ q : ℕ, q ≠ 0 ∧
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

namespace FiniteOrder
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ∞)
    (fun _ => ℕ∞ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≠ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (ρ : ℂ), M.readout () () (analyticOrderAt (completion χ) ρ) ⊤ ∧
      (completion χ ρ = 0 ↔ 0 < analyticOrderNatAt (completion χ) ρ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hn⟩ := nonprincipal_example
  exact (h χ hn 2).1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_zero_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_zero_order,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_zero_order) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_zero_order
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData.FiniteOrder.family
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
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FiniteOrder

namespace Strip
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => True) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {ρ : ℂ}
    (hρ : M.readout () () (completion χ ρ) 0), 0 < ρ.re ∧ ρ.re < 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  have hh := (h hp (ρ := 2) True.intro).2
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_zero_strip) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_zero_strip,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_zero_strip) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_zero_strip
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData.Strip.family
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
      path := #["body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Strip

namespace Reflection
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x * y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (s : ℂ),
    completion χ (1 - conj s) = M.readout () () χ.rootNumber (conj (completion χ s))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (χ := (1 : DirichletCharacter ℂ 1))
    DirichletCharacter.isPrimitive_one_level_one (-1)
  have hn := completion_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ 1)
    (s := 2) (.inr (.inl (by norm_num))) (by norm_num)
  apply hn
  simpa [rejected, realize, map_ofNat,
    show (1 : ℂ) + 1 = 2 by norm_num] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 1
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_reflect) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_reflect,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_reflect) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_reflect
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData.Reflection.family
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
end Reflection

namespace ReflectionOrder
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ∞)
    (fun _ => ℕ∞ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ),
    (completion χ (1 - conj s) = 0 ↔ completion χ s = 0) ∧
      M.readout () () (analyticOrderAt (completion χ) (1 - conj s))
        (analyticOrderAt (completion χ) s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  exact (h hp hn 2).2
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @completion_reflect_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_reflect_order,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_reflect_order) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_reflect_order
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData.ReflectionOrder.family
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
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ReflectionOrder

namespace Resolvent
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x.re + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (σ t : ℝ) (hσ : 1 ≤ σ),
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * (σ - ρ.1.re) /
        ((σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2))
      (M.readout () () (logDeriv (completion χ) ((σ : ℂ) + t * I)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hp, hn⟩ := primitive_example
  letI : NeZero q := ⟨hq⟩
  have he := (completion_vertical_resolvent hp hn 2 0 (by norm_num)).unique (h hp hn 2 0 (by norm_num))
  change (logDeriv (completion χ) (2 + (0 : ℂ) * I)).re =
    (logDeriv (completion χ) (2 + (0 : ℂ) * I)).re + 1 at he
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @completion_vertical_resolvent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @completion_vertical_resolvent,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_vertical_resolvent) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletion.completion_vertical_resolvent
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData.Resolvent.family
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
    owner := `D5.S3.CharacterSums.DirichletCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Resolvent

end Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData
