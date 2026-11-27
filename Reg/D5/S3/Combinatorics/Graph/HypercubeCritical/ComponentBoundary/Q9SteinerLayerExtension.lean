import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension
import Reg.Support.SingleDependentReadout

/-! A concrete affine-plane support witnesses the sensitivity of the unique extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension

open Finset
open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical (booleanWeight)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
  (directions directions_card mem_directions)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
  (selected_neighbor_card)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension
  (extension_card_eq_iff)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Affine lines of the plane over three elements, with point `3a + b` for `(a,b)`. -/
private def containsLine (x : Q 9) : Bool :=
  ([(0, 1, 2), (0, 3, 6), (0, 4, 8), (0, 5, 7), (1, 3, 8), (1, 4, 7),
    (1, 5, 6), (2, 3, 7), (2, 4, 6), (2, 5, 8), (3, 4, 5), (6, 7, 8)] :
      List (Fin 9 × Fin 9 × Fin 9)).any fun (a, b, c) => x a && x b && x c

private abbrev selected (x : Q 9) : Prop :=
  (booleanWeight x = 3 ∧ containsLine x = false) ∨
    (booleanWeight x = 4 ∧ containsLine x = true)

private def support : Finset (Q 9) := univ.filter selected

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem support_card : support.card = 144 := by decide +kernel

private theorem support_band : ∀ x ∈ support, booleanWeight x = 3 ∨ booleanWeight x = 4 := by
  intro x hx
  rcases (mem_filter.mp hx).2 with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem support_flip_count :
    ∀ x : Q 9, selected x → ((univ : Finset (Fin 9)).filter
      (fun i => selected (_root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip x i))).card = 3 := by decide +kernel

noncomputable section
open scoped Classical

private theorem support_regular :
    ((hypercube 9).induce (support : Set (Q 9))).IsRegularOfDegree 3 := by
  intro z
  obtain ⟨x, hx⟩ := z
  have hfilter : support.filter ((hypercube 9).Adj x) =
      (hypercube 9).neighborFinset x ∩ support := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have hdirs : directions support x = univ.filter (fun i => selected (_root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip x i)) := by
    ext i
    simp only [mem_directions, support, mem_filter, mem_univ, true_and]
  rw [← selected_neighbor_card hx, ← hfilter, ← directions_card, hdirs]
  exact support_flip_count x (mem_filter.mp hx).2

private abbrev completion (C : Finset (Q 9)) : Finset (Q 9) :=
  C ∪ univ.filter (fun x => booleanWeight x = 1 ∨ booleanWeight x = 6 ∨ booleanWeight x = 8)

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset (Q 9)) (fun _ => Finset (Q 9))

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ {C A : Finset (Q 9)} (hcard : C.card = 144)
    (hband : ∀ x ∈ C, booleanWeight x = 3 ∨ booleanWeight x = 4)
    (hcubic : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3),
    (C ⊆ A ∧
      (∀ x : (A : Set (Q 9)), ((hypercube 9).induce (A : Set (Q 9))).degree x ≤ 3) ∧
      A.card = 246) ↔ A = r.readout () () C

private def actual : Realization signature :=
  realize signature (fun _ _ C =>
    C ∪ univ.filter (fun x => booleanWeight x = 1 ∨ booleanWeight x = 6 ∨ booleanWeight x = 8))
    Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hsubset :=
    ((law (C := support) (A := ∅) support_card support_band support_regular).mpr rfl).1
  exact (by decide : ¬ (144 ≤ 0))
    (by simpa only [support_card, card_empty] using card_le_card hsubset)

def sourceEvidence : Registration arena (type_of% @extension_card_eq_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extension_card_eq_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    let zero : Q 9 := fun _ => false
    have hzero : booleanWeight zero = 0 := by dsimp [zero]; decide +kernel
    refine ⟨(), ∅, {zero}, ?_⟩
    change completion ∅ ≠ completion {zero}
    intro he
    have hz : zero ∈ completion {zero} := mem_union_left _ (mem_singleton_self _)
    rw [← he] at hz
    simpa [completion, hzero] using hz

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@extension_card_eq_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension.extension_card_eq_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C =>
    C ∪ univ.filter (fun x => booleanWeight x = 1 ∨ booleanWeight x = 6 ∨ booleanWeight x = 8))
    Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension
