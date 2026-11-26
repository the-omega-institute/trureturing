import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the shifted determinant identities and order. -/

namespace Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder

open _root_.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev subtractionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ
    (fun _ => ℝ[X]) (fun _ => ℝ[X])

private theorem subtraction_dependence (offset : ℝ → ℝ[X]) :
    ObservationalDependence subtractionSignature
      (realize subtractionSignature (fun _ lam x => x - offset lam) (fun e => nomatch e)) := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  change (0 : ℝ[X]) - offset 0 ≠ 1 - offset 0
  intro h
  exact zero_ne_one (sub_left_inj.mp h)

namespace Chiral

private abbrev signature := subtractionSignature

private def actual : Realization signature :=
  realize signature (fun _ lam x => x - shiftedDetPolynomial (chiralComparator lam))
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ lam x => (x - shiftedDetPolynomial (chiralComparator lam)) + 1)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam c p q : ℝ}, c ^ 2 + p ^ 2 + q ^ 2 = 1 →
    R.readout () lam (shiftedDetPolynomial (chiral lam c p q)) =
      C (delta2 (lam ^ 2) (invariantX c) (invariantZ c p)) * X ^ 2
      + C (delta3 (lam ^ 2) (invariantX c) (invariantZ c p)) * X
      + C (delta4 (lam ^ 2) (invariantX c) (invariantZ c p) (invariantR c q))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : (1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 1 := by norm_num
  have hbad := @h 0 1 0 0 hn
  dsimp only [rejected, realize] at hbad
  rw [chiral_det_polynomial_difference hn] at hbad
  exact one_ne_zero (add_left_cancel (hbad.trans (add_zero _).symm))

def family : Registration arena (type_of% (@chiral_det_polynomial_difference)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chiral_det_polynomial_difference, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := subtraction_dependence (fun lam => shiftedDetPolynomial (chiralComparator lam))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiral_det_polynomial_difference) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder.chiral_det_polynomial_difference.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder.Chiral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ lam x => x - shiftedDetPolynomial (chiralComparator lam))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Chiral

namespace Complement

private abbrev signature := subtractionSignature

private def actual : Realization signature :=
  realize signature (fun _ lam x => x - shiftedDetPolynomial (complementComparator lam))
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ lam x => (x - shiftedDetPolynomial (complementComparator lam)) + 1)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam c p q : ℝ}, c ^ 2 + p ^ 2 + q ^ 2 = 1 →
    R.readout () lam (shiftedDetPolynomial (complement lam c q)) =
      C (complementDelta (lam ^ 2) (invariantX c) (invariantZ c p))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : (1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 1 := by norm_num
  have hbad := @h 0 1 0 0 hn
  dsimp only [rejected, realize] at hbad
  rw [complement_det_polynomial_difference hn] at hbad
  exact one_ne_zero (add_left_cancel (hbad.trans (add_zero _).symm))

def family : Registration arena (type_of% (@complement_det_polynomial_difference)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complement_det_polynomial_difference, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := subtraction_dependence (fun lam => shiftedDetPolynomial (complementComparator lam))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@complement_det_polynomial_difference) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder.complement_det_polynomial_difference.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder.Complement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ lam x => x - shiftedDetPolynomial (complementComparator lam))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Complement

namespace Order

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

-- The selected chiral comparison varies while the complementary comparison
-- and the full source telescope stay fixed.
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s lam c p q : ℝ}, 0 ≤ s → 0 ≤ lam → lam ≤ 1 →
    c ^ 2 + p ^ 2 + q ^ 2 = 1 →
    R.readout () () (s • (1 : Matrix (Fin 4) (Fin 4) ℝ) + chiralComparator lam).det
        (s • (1 : Matrix (Fin 4) (Fin 4) ℝ) + chiral lam c p q).det ∧
      (s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + complementComparator lam).det ≤
        (s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + complement lam c q).det

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (@h 0 0 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena (type_of% (@det_shift_order)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@det_shift_order, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@det_shift_order) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder.det_shift_order.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder.Order.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Order

end

end Reg.D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
