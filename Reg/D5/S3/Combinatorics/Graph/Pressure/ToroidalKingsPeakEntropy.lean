import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy
import Reg.Support.DependentFamily

/-! The original all-integer convergence law with its numerical sequence readout. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy
open _root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam

namespace Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy

noncomputable section

private theorem singleton_powerset (a : ℕ × ℕ) :
    ({a} : Finset (ℕ × ℕ)).powerset = {∅, {a}} := by
  ext s
  simp [Finset.subset_singleton_iff]


private theorem peak_two_gt_one : 1 < peak 2 := by
  classical
  let S : Finset (Finset (ℕ × ℕ)) := {{(0, 0)}, {(0, 1)}}
  have hsub : S ⊆ (independentSets (board 2) (torusAdjacent 2)).filter
      (fun s => s.card = 1) := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;>
      norm_num [independentSets, board, torusAdjacent]
  have hcard : S.card = 2 := by decide
  have hc : 2 ≤ coefficient 2 1 := by
    have hh := Finset.card_le_card hsub
    rw [hcard] at hh
    exact hh
  have hm : coefficient 2 1 ≤ peak 2 :=
    Finset.le_sup (by decide : 1 ∈ Finset.range (2 ^ 2 + 1))
  omega

private theorem peak_zero : peak 0 = 1 := by
  norm_num [peak, coefficient, independentSets, board, torusAdjacent,
    Finset.filter_singleton]

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => rootGrowth peak n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => a247413 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧
    ∀ n : ℕ, N ≤ n → |r.readout () () n - a247413| < ε

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, hN, hε⟩ := h (1 / 2) (by norm_num)
  have hf := hε N le_rfl
  change |a247413 + 1 - a247413| < (1 : ℝ) / 2 at hf
  rw [show a247413 + 1 - a247413 = 1 by ring] at hf
  norm_num at hf

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  have hr : 1 < rootGrowth peak 2 := by
    apply Real.one_lt_rpow
    · exact_mod_cast peak_two_gt_one
    · norm_num
  change rootGrowth peak 0 ≠ rootGrowth peak 2
  simpa only [rootGrowth, peak_zero, Nat.cast_one, Real.one_rpow] using hr.ne

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_1 : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => rootGrowth peak n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration_1

end
end Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsPeakEntropy
