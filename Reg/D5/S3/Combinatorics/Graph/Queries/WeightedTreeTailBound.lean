import D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Reg.Support.DependentFamily

/-! The target's depth determines the total available leaf weight. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
open _root_.D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound

universe u

private abbrev Leaf (k : ℕ) := {y // y ∈ leafWords k}
private abbrev Vertex (k : ℕ) := {x : List Bool // x.length ≤ k}

private def vertex {k : ℕ} (z : Vertex k) (y : Leaf k) : Vertex k :=
  ⟨y.1, (((weighted_leaf_distance k z).2.1 y.1).mp y.2).le⟩

private abbrev WeightSignature : Signature where
  Params := ℕ
  State := Vertex
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def actualWeight : Realization WeightSignature :=
  realize WeightSignature (fun _ _ z => totalLeafWeight z) (fun e => nomatch e)

private def noWeight : Realization WeightSignature :=
  realize WeightSignature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev WeightArena : Arena where
  signature := WeightSignature
  Law R := ∀ {Ω : Type u} (μ : PMF Ω) (k r : ℕ) (target : Vertex k) (budget : ℝ≥0∞)
    (cross tail : ℕ → Leaf k → Set Ω) (collision : Set Ω)
    (_hCover : ∀ ω ∈ collision, ∃ (j : ℕ) (y : Leaf k),
      j + 1 + (boundedWordTree k).dist target (vertex target y) = r ∧
      ω ∈ cross j y ∧ ω ∈ tail j y)
    (_hCross : ∀ j y, μ.toOuterMeasure (cross j y) ≤ budget)
    (_hTail : ∀ j y, μ.toOuterMeasure (cross j y ∩ tail j y) ≤
      μ.toOuterMeasure (cross j y) *
        ((2 : ℝ≥0∞) ^ (boundedWordTree k).dist target (vertex target y))⁻¹),
    let totalWeight := R.readout () k target
    μ.toOuterMeasure collision ≤ budget * totalWeight

private theorem noWeight_invalid : ¬ WeightArena.{u}.Law noWeight := by
  intro h
  let Ω := ULift.{u} Unit
  let μ : PMF Ω := PMF.pure ⟨()⟩
  let z : Vertex 0 := ⟨[], by simp⟩
  let y₀ : Leaf 0 := ⟨[], by simp [leafWords]⟩
  have hdist (y : Leaf 0) : (boundedWordTree 0).dist z (vertex z y) = 0 := by
    have hlen := ((weighted_leaf_distance 0 z).2.1 y.1).mp y.2
    have hy : vertex z y = z := Subtype.ext (List.length_eq_zero_iff.mp hlen)
    rw [hy, SimpleGraph.dist_self]
  have hMass : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
  have hBad := h μ 0 1 z 1 (fun _ _ => Set.univ) (fun _ _ => Set.univ) Set.univ
    (by
      intro ω hω
      exact ⟨0, y₀, by simp [hdist], hω, hω⟩)
    (by simp [hMass])
    (by simp [hdist, hMass])
  change μ.toOuterMeasure Set.univ ≤ 1 * 0 at hBad
  simp [hMass] at hBad

private theorem weight_varies :
    actualWeight.readout () 1 ⟨[], by simp⟩ ≠
      actualWeight.readout () 1 ⟨[false], by simp⟩ := by
  change ENNReal.ofReal (3 / 2 - (1 / 2 : ℝ)^1) ≠
    ENNReal.ofReal (3 / 2 - (1 / 2 : ℝ)^2)
  rw [show (3 / 2 : ℝ) - (1 / 2 : ℝ)^1 = 1 by norm_num,
    show (3 / 2 : ℝ) - (1 / 2 : ℝ)^2 = 5 / 4 by norm_num, ENNReal.ofReal_one]
  exact ne_of_lt (ENNReal.one_lt_ofReal.mpr (by norm_num))

noncomputable def evidence :
    Registration WeightArena.{u} (type_of% (@mass_of_weighted_tail.{u})) where
  actual := actualWeight
  bridge := Iff.rfl
  variation := ⟨@mass_of_weighted_tail.{u}, noWeight, noWeight_invalid⟩
  sensitivity := ⟨fun i => ⟨noWeight,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, noWeight_invalid⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨1, ⟨[], by simp⟩, ⟨[false], by simp⟩, weight_varies⟩

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@mass_of_weighted_tail.{u}) (Realization WeightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound.mass_of_weighted_tail
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨WeightArena.{u}⟩
  objectArena := .source ⟨WeightArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WeightArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize WeightSignature (fun _ _ z => totalLeafWeight z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Queries.WeightedTreeTailBound
