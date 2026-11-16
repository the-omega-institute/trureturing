import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect
import Reg.Support.DependentFamily

/-! The whole source family varies only its exact profile observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect

open _root_.D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => profile b) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : ℝ), 0 ≤ M → ∀ (ε : ℝ), 0 < ε →
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ H X : Finset ℕ,
      (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ Real.sqrt 2 * Real.sqrt z) →
      (∀ p ∈ X, p.Prime ∧ Real.sqrt 2 * Real.sqrt z < (p : ℝ) ∧ (p : ℝ) ≤ z) →
      (∑ p ∈ H, Real.log p) + (∑ p ∈ X, Real.log p) ≤ M * Real.sqrt z →
      R.readout () () (((∑ p ∈ H, Real.log p) + (∑ p ∈ X, Real.log p)) / Real.sqrt z) ≤
        (Real.sqrt z * Real.log z) *
          ((∑ p ∈ H, ((1 : ℝ) / (p : ℝ) ^ 2 -
              (1 / ((Real.sqrt 2 * Real.sqrt z) ^ 2 *
                Real.log (Real.sqrt 2 * Real.sqrt z))) * Real.log p)) +
            ∑ p ∈ X, ((1 / ((Real.sqrt 2 * Real.sqrt z) ^ 2 *
                Real.log (Real.sqrt 2 * Real.sqrt z))) * Real.log p -
              (1 : ℝ) / (p : ℝ) ^ 2)) + ε

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Z, hZ, hh⟩ := h 0 (by norm_num) (1 / 2) (by norm_num)
  have hb := hh Z le_rfl ∅ ∅ (by simp) (by simp) (by simp)
  change (1 : ℝ) ≤ _ at hb
  simp only [Finset.sum_empty, add_zero, mul_zero] at hb
  norm_num at hb

private theorem profile_zero : profile 0 = 0 := by
  norm_num [profile]
  rw [show (32 : ℝ) = 16 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

private theorem profile_four_pos : 0 < profile 4 := by
  let s := Real.sqrt (1 + (4 : ℝ) ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 17 := by dsimp [s]; norm_num [Real.sq_sqrt]
  have hs4 : 4 < s := by nlinarith only [hs0, hs2]
  have hs3 : s ^ 3 = 17 * s := by
    calc
      _ = s * s ^ 2 := by ring
      _ = _ := by rw [hs2]; ring
  have hden : 0 < s + 1 := by linarith
  have hrad : 32 < (s + 3) ^ 3 / (s + 1) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith only [hs2, hs3, hs4]
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ (s + 3) ^ 3 / (s + 1))
  have hroot0 := Real.sqrt_nonneg ((s + 3) ^ 3 / (s + 1))
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  change 0 < Real.sqrt ((s + 3) ^ 3 / (s + 1)) - 4 * Real.sqrt 2
  nlinarith only [hrad, hroot, hroot0, hr0, hr2]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 4, ?_⟩
  change profile 0 ≠ profile 4
  rw [profile_zero]
  exact ne_of_lt profile_four_pos

def family : Registration arena (type_of% @uniform_prime_occupation_defect) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_prime_occupation_defect, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_prime_occupation_defect) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect.uniform_prime_occupation_defect.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
#print axioms uniform_prime_occupation_defect

end Reg.D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect
