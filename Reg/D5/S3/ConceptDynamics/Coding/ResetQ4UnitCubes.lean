import D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev Plus4 := AdjoinRoot (f 4)
private abbrev Minus4 := AdjoinRoot (g 4)

namespace plus
private def evaluation : Plus4 →+* ZMod 7 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 7)) 5
    (by norm_num [f, S, Finset.sum_range_succ]; decide)
private theorem eval_alpha : evaluation (alpha : Plus4) = 5 := by
  change evaluation (AdjoinRoot.mk (f 4) X) = 5
  simp [evaluation, AdjoinRoot.lift_mk]
private theorem eval_B : evaluation (Bplus : Plus4) = 6 := by
  change evaluation (AdjoinRoot.mk (f 4) (1 + X)) = 6
  norm_num [evaluation, AdjoinRoot.lift_mk]
private theorem alpha_ne_one : alpha ≠ 1 := by
  intro h
  have he := congrArg (fun u : Plus4ˣ => evaluation (u : Plus4)) h
  simp only [eval_alpha, Units.val_one, map_one] at he
  exact (by decide : (5 : ZMod 7) ≠ 1) he
private theorem finite_obstruction :
    ∀ (j : Fin 3) (x : ZMod 7), (5 : ZMod 7) ≠ 6 ^ j.val * x ^ 3 := by decide

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Plus4ˣ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ i => alpha ^ i.val) (fun e => nomatch e)
abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ u : Plus4ˣ, ∃ i j : Fin 3, ∃ v : Plus4ˣ,
    u = r.readout () () i * Bplus ^ j.val * v ^ 3
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨i, j, v, hv⟩ := h alpha
  change alpha = 1 * Bplus ^ j.val * v ^ 3 at hv
  simp only [one_mul] at hv
  have he := congrArg (fun u : Plus4ˣ => evaluation (u : Plus4)) hv
  have he' : (5 : ZMod 7) = 6 ^ j.val * evaluation (v : Plus4) ^ 3 := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
      eval_alpha, eval_B] using he
  exact finite_obstruction j _ he'
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change alpha ^ 0 ≠ alpha ^ 1
  simpa only [pow_zero, pow_one, ne_eq, eq_comm] using alpha_ne_one

def evidence : Registration arena (type_of% @plus_cube_normal_form) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨plus_cube_normal_form, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@plus_cube_normal_form) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.plus.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.plus.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => alpha ^ i.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end plus

namespace minus
private def evaluation : Minus4 →+* ZMod 31 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 31)) 2
    (by norm_num [g, S, Finset.sum_range_succ]; decide)
private theorem eval_B : evaluation (Bminus : Minus4) = 3 := by
  change evaluation (AdjoinRoot.mk (g 4) (1 + X)) = 3
  norm_num [evaluation, AdjoinRoot.lift_mk]
private theorem B_ne_one : Bminus ≠ 1 := by
  intro h
  have he := congrArg (fun u : Minus4ˣ => evaluation (u : Minus4)) h
  simp only [eval_B, Units.val_one, map_one] at he
  exact (by decide : (3 : ZMod 31) ≠ 1) he
private theorem finite_obstruction : ∀ x : ZMod 31, (3 : ZMod 31) ≠ x ^ 3 := by decide

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Minus4ˣ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ i => Bminus ^ i.val) (fun e => nomatch e)
abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ u : Minus4ˣ, ∃ k : Fin 3, ∃ v : Minus4ˣ,
    u = r.readout () () k * v ^ 3
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨k, v, hv⟩ := h Bminus
  change Bminus = 1 * v ^ 3 at hv
  simp only [one_mul] at hv
  have he := congrArg (fun u : Minus4ˣ => evaluation (u : Minus4)) hv
  have he' : (3 : ZMod 31) = evaluation (v : Minus4) ^ 3 := by
    simpa only [Units.val_pow_eq_pow_val, map_pow, eval_B] using he
  exact finite_obstruction _ he'
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Bminus ^ 0 ≠ Bminus ^ 1
  simpa only [pow_zero, pow_one, ne_eq, eq_comm] using B_ne_one

def evidence : Registration arena (type_of% @minus_cube_normal_form) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨minus_cube_normal_form, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@minus_cube_normal_form) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.minus.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.minus.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => Bminus ^ i.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end minus

namespace compatible
abbrev signature := plus.signature
abbrev actual := plus.actual
abbrev bad := plus.bad
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : Plus4ˣ) (w : Minus4ˣ),
    Units.map (rplus 4).toMonoidHom u = Units.map (rminus 4).toMonoidHom w →
    ∃ i j k : Fin 3, ∃ v : Plus4ˣ, ∃ t : Minus4ˣ,
      u = r.readout () () i * Bplus ^ j.val * v ^ 3 ∧
      w = Bminus ^ k.val * t ^ 3 ∧ (j.val : ZMod 3) = (k.val : ZMod 3)
private theorem root_compatible :
    Units.map (rplus 4).toMonoidHom alpha = Units.map (rminus 4).toMonoidHom beta := by
  apply Units.ext
  change rplus 4 (AdjoinRoot.mk (f 4) X) = rminus 4 (AdjoinRoot.mk (g 4) X)
  unfold rplus rminus AdjoinRoot.mk
  exact (Ideal.Quotient.lift_mk _ _ _).trans (Ideal.Quotient.lift_mk _ _ _).symm
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨i, j, k, v, t, hu, hw, hjk⟩ := h alpha beta root_compatible
  change alpha = 1 * Bplus ^ j.val * v ^ 3 at hu
  simp only [one_mul] at hu
  have he := congrArg (fun u : Plus4ˣ => plus.evaluation (u : Plus4)) hu
  have he' : (5 : ZMod 7) = 6 ^ j.val * plus.evaluation (v : Plus4) ^ 3 := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
      plus.eval_alpha, plus.eval_B] using he
  exact plus.finite_obstruction j _ he'
def evidence : Registration arena (type_of% @compatible_cube_normal_forms) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compatible_cube_normal_forms, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := plus.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@compatible_cube_normal_forms) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.compatible.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.compatible.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => alpha ^ i.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end compatible
end Reg.D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
