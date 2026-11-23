import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior
import Reg.Support.SingleDependentReadout

/-! The readout tests whether the ambient support contains the supplied grid. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior

open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
  (Q IsBalanced)

local notation "cubeFlip" =>
  _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip
local notation "cubeFlipFlip" =>
  _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip_flip
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
  (directions directions_card mem_directions)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity
  (gridHigh gridMiddle gridSupport)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior
  (selectedLiftLabels exterior_lift_direction_exclusion)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private matrix_flip_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n : Nat, Finset (Q n))
    (fun p => Finset (Q p.1)) (fun _ => Bool)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} (D : Finset (Q n)) (X : Q n) (d : Bool × Fin 3 → Fin n),
    Function.Injective d → IsBalanced D →
    R.readout () ⟨n, D⟩ (gridSupport X d) = true →
    (∀ s k, (directions D (gridHigh X d (s, k))).card ≤ 3) →
    ∀ (e : Fin n), e ∉ Set.range d → ∀ i j : Fin 3,
    cubeFlip (gridMiddle X d (i, j)) e ∈ D →
    let labels := selectedLiftLabels D X d e i j
    let next := directions D (cubeFlip (gridMiddle X d (i, j)) e)
    Disjoint (labels.image d) next ∧
      (next ∩ Finset.univ.image d).card ≤ 6 - labels.card

private def actual : Realization signature :=
  realize signature (fun _ p C => decide (C ⊆ p.2)) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) Empty.elim

private def witnessAxes (h : Bool × Fin 3) : Fin 7 :=
  ⟨(if h.1 then 3 else 0) + h.2.val, by cases h.1 <;> simp <;> omega⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let X : Q 7 := fun _ => false
  let e : Fin 7 := 6
  let y := cubeFlip (gridMiddle X witnessAxes (0, 0)) e
  let D : Finset (Q 7) := {y, cubeFlip y 0}
  have hy : y ∈ D := Finset.mem_insert_self _ _
  have hz : cubeFlip y 0 ∈ D := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have haxes : Function.Injective witnessAxes := by decide
  have he : e ∉ Set.range witnessAxes := by
    rintro ⟨⟨s, k⟩, h⟩
    have hval := congrArg Fin.val h
    change (if s then 3 else 0) + k.val = 6 at hval
    have hk := k.isLt
    cases s <;> simp at hval <;> omega
  have hbal : IsBalanced D := by
    refine ⟨fun _ => 1, fun _ _ => Or.inl rfl, ?_⟩
    intro u hu v hv huv
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv.ne rfl).elim
    · simpa only [mul_one] using matrix_flip_zero y
    · simpa only [cubeFlipFlip, mul_one] using matrix_flip_zero (cubeFlip y 0)
    · exact (huv.ne rfl).elim
  have hdegree (s : Bool) (k : Fin 3) :
      (directions D (gridHigh X witnessAxes (s, k))).card ≤ 3 := by
    classical
    rw [directions_card]
    have hcard : D.card ≤ 2 := by
      simpa only [D, Finset.card_singleton] using
        (Finset.card_insert_le y {cubeFlip y 0})
    exact (Finset.card_filter_le _ _).trans (hcard.trans (by decide))
  have hdis := (law D X witnessAxes haxes hbal rfl hdegree e he 0 0 hy).1
  have hlabel : (false, 0) ∈ selectedLiftLabels D X witnessAxes e 0 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  have haxis : (0 : Fin 7) ∈ (selectedLiftLabels D X witnessAxes e 0 0).image witnessAxes :=
    Finset.mem_image.mpr ⟨(false, 0), hlabel, rfl⟩
  exact Finset.disjoint_left.mp hdis haxis ((mem_directions D y 0).mpr hz)

def sourceEvidence : Registration arena (type_of% @exterior_lift_direction_exclusion) where
  actual := actual
  bridge := by simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro n D X d hd hb hg hdegree e he i j hy
    exact exterior_lift_direction_exclusion D X d hd hb (of_decide_eq_true hg) hdegree e he i j hy,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    let x : Q 0 := fun _ => false
    refine ⟨⟨0, ∅⟩, ∅, {x}, ?_⟩
    simp [actual, realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exterior_lift_direction_exclusion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior.exterior_lift_direction_exclusion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/--
info: 'Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior.registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms registration

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior
