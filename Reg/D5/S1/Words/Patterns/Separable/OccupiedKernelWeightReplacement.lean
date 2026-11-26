import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The stored readout is the exact residual for the leading jump coefficient. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement


open _root_.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => actualWeightError A) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∃ A > (0 : ℝ), ∃ E : ℝ, 0 ≤ E ∧
    ∀ β : ℝ, 1 / 2 ≤ β → β ≤ 3 / 4 → ∀ n : ℕ, 0 < n →
    let e (i : ℕ) := |R.readout () () A (i + 1) * secondDiff β (n : ℝ) ((i + 1 : ℕ) : ℝ)|
    Summable e ∧ (∑' i, e i) ≤ 298 * E * (n : ℝ) ^ (-β - 3 / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨A, _, E, _, h⟩
  have hs : Summable (fun i : ℕ => |secondDiff (1 / 2) 1 ((i + 1 : ℕ) : ℝ)|) := by
    simpa [rejected, realize] using (h (1 / 2) (by norm_num) (by norm_num) 1 (by norm_num)).1
  have ht (c : ℝ) : Tendsto (fun i : ℕ => ((i : ℝ) + c) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)
  let C := 2 * (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have hseq (i : ℕ) :
      secondDiff (1 / 2) 1 ((i + 1 : ℕ) : ℝ) =
        ((i : ℝ) + 4) ^ (-(1 / 2 : ℝ)) + ((i : ℝ) + 2) ^ (-(1 / 2 : ℝ)) - C := by
    unfold secondDiff C
    push_cast
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + ((i : ℝ) + 1)),
      abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) i] :
        (1 : ℝ) - ((i : ℝ) + 1) ≤ 0), abs_one]
    norm_num only
    rw [show (2 : ℝ) + (1 + ((i : ℝ) + 1)) = (i : ℝ) + 4 by ring,
      show (2 : ℝ) + -(1 - ((i : ℝ) + 1)) = (i : ℝ) + 2 by ring]
  have ht' : Tendsto (fun i : ℕ => secondDiff (1 / 2) 1 ((i + 1 : ℕ) : ℝ)) atTop (𝓝 (-C)) := by
    simp_rw [hseq]
    simpa using ((ht 4).add (ht 2)).sub_const C
  have hz := tendsto_nhds_unique hs.tendsto_atTop_zero ht'.abs
  have hC : 0 < C := by dsimp [C]; positivity
  rw [abs_neg, abs_of_pos hC] at hz
  exact hC.ne hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  change actualWeightError 0 1 = actualWeightError 1 1 at he
  norm_num [actualWeightError] at he
  linarith

def family : Registration arena (type_of% @actual_global_weight_replacement) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_global_weight_replacement, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_global_weight_replacement) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => actualWeightError A) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "arg", "body", "body", "body", "body", "body",
        "value", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

namespace SampleHomogeneity

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior (sample)

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ β => sample β) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 1) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ {β n m : ℝ}, 0 < n → 0 < m →
    R.readout () () β (2 / n) (m / n) =
      n ^ (β + (3 / 2 : ℝ)) * (m ^ (-(3 / 2 : ℝ)) * secondDiff β n m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (β := 0) (n := 1) (m := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize, secondDiff] at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1 / 2, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) 2
  change sample 0 0 2 = sample (1 / 2) 0 2 at he
  have hp : 0 < (2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hq : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hnorm : |1 - (2 : ℝ)| = 1 := by norm_num
  simp only [sample, hnorm, neg_zero, Real.rpow_zero, zero_add, Real.one_rpow] at he
  norm_num only [show 1 + (2 : ℝ) = 3 by norm_num] at he
  have hneg : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * ((3 : ℝ) ^ (-(1 / 2 : ℝ)) + 1 - 2 * 1) < 0 :=
    mul_neg_of_pos_of_neg hp (by linarith)
  linarith

def family : Registration arena (type_of% @sample_eq_lattice) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sample_eq_lattice, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sample_eq_lattice) (Realization signature) (Type) Unit where
  unitName :=
    `Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement.SampleHomogeneity.unit
  realizationName :=
    `Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement.SampleHomogeneity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ β => sample β) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end SampleHomogeneity

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
