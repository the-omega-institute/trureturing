import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell
import Reg.Support.DependentFamily

/-! Typed source-bound audit attempt for the unchanged first-cell theorem.
The source telescope is retained in `arena.Law`; producer source-selection and
binding validation remain separate from this kernel-checked registration. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell

open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (tail)
open _root_.D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open _root_.D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell
open _root_.D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop × ℕ
  Anchor := Unit
  finiteAnchor := inferInstance

def goal (z : ℝ) (n : ℕ) : Prop :=
  let A := tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
    fullPrimePowerResidual z
  let K := Real.log (Real.log z) + (Real.log (n : ℝ) - z) / (z * Real.log z) -
    Real.log (Real.log (Real.log (n : ℝ)))
  (1 / 2 : ℝ) < Real.sqrt z * Real.log z * (A - K)

def actual : Realization signature :=
  realize signature (fun _ z n => (goal z n, n)) (fun _ _ => 0)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (True, 0)) (fun _ _ => 1)

def readout_bad : Realization signature :=
  realize signature (fun _ _ _ => (True, 0)) (fun _ _ => 0)

def anchor_bad : Realization signature :=
  realize signature (fun _ z n => (goal z n, n)) (fun _ _ => 1)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ {z : ℝ}, 11 < z → z ≤ 13 → {n : ℕ} → 0 < n →
      n.primeFactors = Nat.primesLE ⌊z⌋₊ →
      0 < Real.log (n : ℝ) - z →
      Real.log (n : ℝ) - z < 1 / 2 →
      (R.readout () z n).1) ∧
    (∀ (z : ℝ) (n : ℕ), (R.readout () z n).1 = goal z n) ∧
    (∀ z : ℝ, R.anchor () z = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.2.1 0 0
  change True = goal 0 0 at he
  norm_num [goal] at he

private theorem readout_bad_law : ¬ arena.Law readout_bad := by
  intro h
  have he := h.2.1 0 0
  change True = goal 0 0 at he
  norm_num [goal] at he

private theorem actual_law : arena.Law actual := by
  constructor
  · intro z hz hz13 n hn hsupport hM hMhalf
    exact @original_half_surplus_first_cell z hz hz13 n hn hsupport hM hMhalf
  · constructor
    · intro z n
      rfl
    · intro z
      rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (goal 0 0, 0) ≠ (goal 0 1, 1)
  intro h
  exact Nat.noConfusion (congrArg Prod.snd h)

def family : Registration arena (type_of% (@original_half_surplus_first_cell)) where
  actual := actual
  bridge := by
    constructor
    · intro h
      exact ⟨h, ⟨by intro z n; rfl, by intro z; rfl⟩⟩
    · intro h
      exact h.1
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨readout_bad, ?_, ?_, ?_⟩
      · intro j hji
        exact (hji (Subsingleton.elim _ _)).elim
      · rfl
      · intro h
        exact readout_bad_law h
    · intro i
      refine ⟨anchor_bad, ?_, ?_, ?_⟩
      · rfl
      · intro j hji
        exact (hji (Subsingleton.elim _ _)).elim
      · intro h
        have hz := h.2.2 0
        change (1 : ℕ) = 0 at hz
        omega
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_half_surplus_first_cell)
    (type_of% (realize signature (fun _ z n => (goal z n, n)) (fun _ _ => 0)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell.original_half_surplus_first_cell.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z n => (goal z n, n)) (fun _ _ => 0))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell
