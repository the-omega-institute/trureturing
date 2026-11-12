import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover

/-! Source-owner audit registration for the finite circle-cover theorem. -/

namespace Reg.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover

open _root_.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Σ theta : ℝ, Σ t : ℝ, Σ w : ℝ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s =>
    ∃ ell : ℤ, p.2.1 < (s : ℝ) * p.1 - (ell : ℝ) ∧
      (s : ℝ) * p.1 - (ell : ℝ) < p.2.1 + p.2.2.1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (theta t w : ℝ) (N : ℕ),
    0 < w → 4 / w ≤ (N : ℝ) →
      (∀ h a : ℤ, 1 ≤ h → h ≤ ⌈(4 : ℝ) / w⌉ →
        1 / (N : ℝ) < |(h : ℝ) * theta - (a : ℝ)|) →
      ∃ b : ℕ, N ≤ b ∧ b ≤ 2 * N ∧
        R.readout () ⟨theta, t, w, N⟩ b

abbrev sourceScope :=
  type_of% (@_root_.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover.quantitative_finite_circle_cover)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h theta t w N hw hbudget havoid
    obtain ⟨b, hbN, hb2, ell, hlt, hlt2⟩ :=
      h theta t w N hw hbudget havoid
    exact ⟨b, hbN, hb2, by
      exact ⟨ell, hlt, hlt2⟩⟩
  · intro h theta t w N hw hbudget havoid
    obtain ⟨b, hbN, hb2, hinterval⟩ :=
      h theta t w N hw hbudget havoid
    obtain ⟨ell, hlt, hlt2⟩ := hinterval
    exact ⟨b, hbN, hb2, ell, hlt, hlt2⟩

/-- A readout erased to false cannot satisfy the source law. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

theorem havoid_1_over_33 :
    ∀ h a : ℤ, 1 ≤ h → h ≤ (32 : ℤ) →
      (1 : ℝ) / 1000 < |(h : ℝ) * ((1 : ℝ) / 33) - (a : ℝ)| := by
  intro h a hh1 hh32
  have hh1R : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hh32R : (h : ℝ) ≤ 32 := by exact_mod_cast hh32
  by_cases ha : a ≤ 0
  · have haR : (a : ℝ) ≤ 0 := by exact_mod_cast ha
    have hnonneg : 0 ≤ (h : ℝ) * ((1 : ℝ) / 33) - (a : ℝ) := by
      nlinarith [hh1R]
    rw [abs_of_nonneg hnonneg]
    have hbase : (1 : ℝ) / 1000 < (1 : ℝ) / 33 := by norm_num
    have hmul : (1 : ℝ) / 33 ≤ (h : ℝ) * ((1 : ℝ) / 33) := by
      nlinarith
    linarith
  · have ha1 : (1 : ℤ) ≤ a := by omega
    have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hnonpos : (h : ℝ) * ((1 : ℝ) / 33) - (a : ℝ) ≤ 0 := by
      have hfrac : (h : ℝ) * ((1 : ℝ) / 33) ≤ 32 / 33 := by
        nlinarith
      have hlt : (32 : ℝ) / 33 < 1 := by norm_num
      linarith
    rw [abs_of_nonpos hnonpos]
    have hbase : (1 : ℝ) / 1000 < (1 : ℝ) / 33 := by norm_num
    have hmul : (h : ℝ) * ((1 : ℝ) / 33) ≤ (a : ℝ) - (1 : ℝ) / 33 := by
      have hfrac : (h : ℝ) * ((1 : ℝ) / 33) ≤ 32 / 33 := by
        nlinarith
      nlinarith
    linarith

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hhavoid : ∀ h a : ℤ, 1 ≤ h → h ≤ ⌈(4 : ℝ) / ((1 : ℝ) / 8)⌉ →
      (1 : ℝ) / 1000 < |(h : ℝ) * ((1 : ℝ) / 33) - (a : ℝ)| := by
    norm_num
    exact havoid_1_over_33
  have hh := h ((1 : ℝ) / 33) 0 ((1 : ℝ) / 8) 1000 (by norm_num)
    (by norm_num) hhavoid
  obtain ⟨b, hbN, hb2, ell, hbad⟩ := hh

def source_registration :
    Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (by exact
    @_root_.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover.quantitative_finite_circle_cover),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨⟨(1 : ℝ) / 2, 0, (3 : ℝ) / 4, 1⟩, 1, 0, ?_⟩
    intro heq
    have htrue : actual.readout () ⟨(1 : ℝ) / 2, 0, (3 : ℝ) / 4, 1⟩ 1 := by
      refine ⟨0, by norm_num, by norm_num⟩
    rw [heq] at htrue
    have hfalse := htrue
    obtain ⟨ell, hlt, hlt2⟩ := hfalse
    have hell0 : ell < 0 := by
      exact_mod_cast (show (ell : ℝ) < 0 by nlinarith [hlt])
    have hellm1 : (-1 : ℤ) < ell := by
      exact_mod_cast (show (-1 : ℝ) < (ell : ℝ) by nlinarith [hlt2])
    omega

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover.quantitative_finite_circle_cover)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover.quantitative_finite_circle_cover.__information_unit
  realizationName := `Reg.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s =>
    ∃ ell : ℤ, p.2.1 < (s : ℝ) * p.1 - (ell : ℝ) ∧
      (s : ℝ) * p.1 - (ell : ℝ) < p.2.1 + p.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover
