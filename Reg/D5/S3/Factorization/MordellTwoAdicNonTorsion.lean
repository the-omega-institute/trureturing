import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.MordellTwoAdicNonTorsion
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion

open _root_.D5.S3.Factorization.MordellTwoAdicNonTorsion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e)

def rejectedX : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def rejectedY : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem torsion_example :
    ∃ h : (mordellCurve (-1)).Nonsingular (1 : ℚ) 0,
      IsOfFinAddOrder (.some 1 0 h : (mordellCurve (-1)).Point) := by
  have hns : (mordellCurve (-1)).Nonsingular (1 : ℚ) 0 := by
    apply ((mordellCurve (-1)).nonsingular_iff' _ _).2
    constructor
    · apply ((mordellCurve (-1)).equation_iff _ _).2
      norm_num [mordellCurve]
    · left
      norm_num [mordellCurve]
  refine ⟨hns, isOfFinAddOrder_iff_nsmul_eq_zero.mpr ?_⟩
  refine ⟨2, by decide, ?_⟩
  have hdouble :
      (.some 1 0 hns : (mordellCurve (-1)).Point) +
        (.some 1 0 hns : (mordellCurve (-1)).Point) = 0 :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      (W := mordellCurve (-1)) (by norm_num [mordellCurve, WeierstrassCurve.Affine.negY])
  simpa only [two_nsmul] using hdouble

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : ℚ), (2 : ℚ), ?_⟩
  change padicValRat 2 (1 : ℚ) ≠ padicValRat 2 (2 : ℚ)
  rw [padicValRat.one]
  change (0 : ℤ) ≠ padicValRat 2 ((2 : ℕ) : ℚ)
  rw [padicValRat.of_nat]
  norm_num [padicValNat_self]

def xArena : Arena where
  signature := signature
  Law r := ∀ (b : ℤ) {x y : ℚ} (h : (mordellCurve b).Nonsingular x y),
    r.readout () () x < 0 →
      ¬ IsOfFinAddOrder (.some x y h : (mordellCurve b).Point)

private theorem rejected_x_law : ¬ xArena.Law rejectedX := by
  intro h
  obtain ⟨hns, htor⟩ := torsion_example
  have hbad := h (-1) (x := 1) (y := 0) hns (by norm_num [rejectedX, realize])
  exact hbad htor

def xRegistration : Registration xArena (xArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨infinite_add_order_of_negative_two_adic_x, rejectedX, rejected_x_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedX, ?_, rfl, rejected_x_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x) (type_of% (xArena)) (type_of% (xArena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "MordellTwoAdicNonTorsion") "infinite_add_order_of_negative_two_adic_x") "Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion/Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(xArena)⟩,
  objectArena := ⟨(xArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (xArena) ⟨(xRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


def yArena : Arena where
  signature := signature
  Law r := ∀ (b : ℤ) {x y : ℚ} (h : (mordellCurve b).Nonsingular x y)
    (hx0 : x ≠ 0) (hx : padicValRat 2 x = 0),
    0 < r.readout () () y →
      ¬ IsOfFinAddOrder (.some x y h : (mordellCurve b).Point)

private theorem rejected_y_law : ¬ yArena.Law rejectedY := by
  intro h
  obtain ⟨hns, htor⟩ := torsion_example
  have hbad := h (-1) (x := 1) (y := 0) hns (by norm_num)
    (by simp [padicValRat.one]) (by norm_num [rejectedY, realize])
  exact hbad htor

def yRegistration : Registration yArena (yArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨infinite_add_order_of_unit_x_positive_two_adic_y, rejectedY, rejected_y_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedY, ?_, rfl, rejected_y_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y) (type_of% (yArena)) (type_of% (yArena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "MordellTwoAdicNonTorsion") "infinite_add_order_of_unit_x_positive_two_adic_y") "Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion/Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(yArena)⟩,
  objectArena := ⟨(yArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (yArena) ⟨(yRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "domain", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms xRegistration
#print axioms yRegistration

end Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion
