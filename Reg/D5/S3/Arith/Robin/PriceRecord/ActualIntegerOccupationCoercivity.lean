import D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

open Real Finset
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The square-root observation in the quantitative bound, with z retained. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => sqrt d) (fun e => nomatch e)

/-- Intervene on this observation over the complete family of scales and defects. -/
def rejected : Realization signature :=
  realize signature (fun _ z d => -(8 * d + 32 / log z + 1) / 6)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ n : ℕ, 1 ≤ n →
    ∀ H X : Finset ℕ,
    (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ sqrt 2 * sqrt z ∧ n.factorization p ≤ 1) →
    (∀ p ∈ X, p.Prime ∧ sqrt 2 * sqrt z < (p : ℝ) ∧ 2 ≤ n.factorization p) →
    ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) / sqrt z ≤
      6 * R.readout () z (sqrt z * log z * actualDefect z n) +
        8 * (sqrt z * log z * actualDefect z n) + 32 / log z

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨Z, hZ, h⟩
  have hb := h Z le_rfl 1 le_rfl ∅ ∅ (by simp) (by simp)
  simp only [sum_empty, add_zero, zero_div] at hb
  change (0 : ℝ) ≤
    6 * (-(8 * (sqrt Z * log Z * actualDefect Z 1) + 32 / log Z + 1) / 6) +
      8 * (sqrt Z * log Z * actualDefect Z 1) + 32 / log Z at hb
  linarith only [hb]

def family : Registration arena (type_of% (@eventually_quantitative_actual_occupation_defect)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventually_quantitative_actual_occupation_defect, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(2 : ℝ), 0, 1, ?_⟩
    change sqrt (0 : ℝ) ≠ sqrt 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventually_quantitative_actual_occupation_defect) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.eventually_quantitative_actual_occupation_defect.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => sqrt d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit


open _root_.D5.S3.Arith.GoldenLocalThreshold
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference

namespace CountAudit

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ params a => goldenPrimeLocalObjective params.1 params.2 a) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ params a => goldenPrimeLocalObjective params.1 params.2 a - 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam : ℝ}, 0 < lam → ∀ {p : ℕ}, p.Prime → ∀ a : ℕ,
    goldenPrimeLocalObjective lam p a ≤ R.readout () ⟨lam, p⟩ (optimalLayerCount lam p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (lam := 1) (by norm_num) (p := 2) Nat.prime_two (optimalLayerCount 1 2)
  change goldenPrimeLocalObjective 1 2 (optimalLayerCount 1 2) ≤
    goldenPrimeLocalObjective 1 2 (optimalLayerCount 1 2) - 1 at hb
  linarith only [hb]

def family : Registration arena (type_of% (@count_maximal)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_maximal, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, 2⟩, 0, 1, ?_⟩
    change goldenPrimeLocalObjective 0 2 0 ≠ goldenPrimeLocalObjective 0 2 1
    have hlog : 0 < log (3 / 2 : ℝ) := log_pos (by norm_num)
    norm_num [goldenPrimeLocalObjective]
    exact (ne_of_gt hlog).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@count_maximal) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.count_maximal.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.CountAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ params a => goldenPrimeLocalObjective params.1 params.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end CountAudit

namespace DefectObservation

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ z n => actualDefect z n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change actualDefect 1 1 ≠ actualDefect 1 2
  have hlog : 0 < log (3 / 2 : ℝ) := log_pos (by norm_num)
  simp only [actualDefect]
  rw [golden_resource_sigma_identity _ (by norm_num : 1 ≤ 1),
    golden_resource_sigma_identity _ (by norm_num : 1 ≤ 2)]
  norm_num [referencePrice, ArithmeticFunction.sigma_one_apply,
    show (2 : ℕ).divisors = {1, 2} by decide]
  linarith

end DefectObservation

namespace LocalGapAudit

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := ∀ {z : ℝ}, 1 < z → ∀ {n : ℕ}, 1 ≤ n →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    (∑ p ∈ S, (goldenPrimeLocalObjective (referencePrice z) p
        (optimalLayerCount (referencePrice z) p) -
      goldenPrimeLocalObjective (referencePrice z) p (n.factorization p))) ≤
        R.readout () z n

private theorem rejected_law : ¬ arena.Law DefectObservation.rejected := by
  intro h
  have hb := h (z := 2) (by norm_num) (n := 1) le_rfl ∅ (by simp)
  change (∑ p ∈ (∅ : Finset ℕ), _) ≤ (-1 : ℝ) at hb
  have hb' : (0 : ℝ) ≤ -1 := by simpa only [sum_empty] using hb
  norm_num at hb' 

def family : Registration arena (type_of% (@actual_local_gap_sum_le_defect)) where
  actual := DefectObservation.actual
  bridge := Iff.rfl
  variation := ⟨actual_local_gap_sum_le_defect, DefectObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨DefectObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := DefectObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_local_gap_sum_le_defect) (Realization DefectObservation.signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.actual_local_gap_sum_le_defect.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.LocalGapAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DefectObservation.signature (fun _ z n => actualDefect z n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end LocalGapAudit

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
