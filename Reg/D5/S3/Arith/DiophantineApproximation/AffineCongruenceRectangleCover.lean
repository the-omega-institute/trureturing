import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover
import Mathlib.Tactic

/-! Source registration for the reciprocal width in the denominator bound. -/

namespace Reg.D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover

open LeanInformationAudit
open _root_.D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover
  (RectangleHit ShortLabel delta errorSum phase radius short_label_miss_obstruction)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => 1 / w) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N M : ℕ} {theta phi t w : ℝ}
    (hw : 0 < w ∧ w < 1)
    (hNw : (4 : ℝ) ≤ (N : ℝ) * w) (hMw : (4 : ℝ) ≤ (M : ℝ) * w)
    (hmiss : ¬ RectangleHit N M theta phi t w),
    ∃ L : ShortLabel N M theta phi w,
      (∀ L' : ShortLabel N M theta phi w, L' = L) ∧
      (∀ n : ℤ, radius N M L.h L.p3 L.p5 theta phi w -
        (L.h : ℝ) * errorSum L.h L.p3 L.p5 theta phi ≤
        |(n : ℝ) - phase N M L.h L.p3 L.p5 theta phi t w|) ∧
      ((L.h : ℝ) * w + ((N : ℝ) - 2 * (L.h : ℝ)) * |delta L.h theta L.p3| +
        ((M : ℝ) - 2 * (L.h : ℝ)) * |delta L.h phi L.p5| ≤ 1) ∧
      (L.h : ℝ) ≤ R.readout () () w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmiss : ¬ RectangleHit 8 8 0 0 0 (1 / 2) := by
    unfold RectangleHit
    rintro ⟨a, b, d, _, _, _, _, ha0, ha1⟩
    simp only [mul_zero, add_zero, zero_sub] at ha0 ha1
    have ha0z : (0 : ℤ) < -a := by exact_mod_cast ha0
    have ha1z : (1 : ℤ) ≤ -a := by omega
    have ha1r : (1 : ℝ) ≤ -(a : ℝ) := by exact_mod_cast ha1z
    linarith only [ha1, ha1r]
  obtain ⟨L, _, _, _, hbound⟩ :=
    @h 8 8 0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) hmiss
  have hpos : (1 : ℝ) ≤ (L.h : ℝ) := by exact_mod_cast L.positive
  change (L.h : ℝ) ≤ 0 at hbound
  linarith only [hpos, hbound]

def family : Registration arena (type_of% (@short_label_miss_obstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@short_label_miss_obstruction, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1 / 4, 1 / 2, ?_⟩
    change (1 : ℝ) / (1 / 4) ≠ 1 / (1 / 2)
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@short_label_miss_obstruction) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover.short_label_miss_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => 1 / w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover
