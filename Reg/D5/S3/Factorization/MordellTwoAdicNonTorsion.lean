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

register_information_theorem
  _root_.D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x
  in xArena
  readout via (realize signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e))
  realizes xRegistration
  escape from source ({
    owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

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

register_information_theorem
  _root_.D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y
  in yArena
  readout via (realize signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e))
  realizes yRegistration
  escape from source ({
    owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms xRegistration
#print axioms yRegistration

end Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion
