import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.OriginalSignedCompressedFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The complete signed mode telescope is retained; the observed state is
physical shift h, rather than a finite truncation of the integral. -/
abbrev signature : Signature where
  Params := ℝ × ℤ × ℤ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p h => entry p.1 p.2.1 p.2.2 h) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ) (_hL : 0 < L) (m n : ℤ) (h : ℝ),
    R.readout () ⟨L, m, n⟩ h = matrix L m n h

private lemma matrix_at_origin : matrix 1 0 0 0 = 1 := by
  simp only [matrix, abs_zero, show ¬ (1 : ℝ) ≤ 0 by norm_num, if_false,
    le_refl, if_true, sub_zero, div_self (by norm_num : (1 : ℝ) ≠ 0),
    Complex.ofReal_one, one_mul, neg_zero]
  change Complex.exp (((frequency 1 0 * 0 : ℝ) : ℂ) * Complex.I) = 1
  simp

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 (by norm_num) 0 0 0
  rw [matrix_at_origin] at hz
  norm_num [rejected, realize] at hz

private lemma actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0, 0⟩, 0, 1, ?_⟩
  change entry 1 0 0 0 ≠ entry 1 0 0 1
  rw [entry_eq_matrix 1 (by norm_num), matrix_at_origin,
    entry_disjoint 1 0 0 1 (by norm_num)]
  norm_num

def family : Registration arena
    (type_of% (@_root_.OriginalSignedCompressedFourier.entry_eq_matrix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨entry_eq_matrix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.OriginalSignedCompressedFourier.entry_eq_matrix)
    (type_of% (realize signature
      (fun _ p h => entry p.1 p.2.1 p.2.2 h) (fun e => nomatch e))) Type Unit where
  unitName := `OriginalSignedCompressedFourier.entry_eq_matrix.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p h => entry p.1 p.2.1 p.2.2 h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier
