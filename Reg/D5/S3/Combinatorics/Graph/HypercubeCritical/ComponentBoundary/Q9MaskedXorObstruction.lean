import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction
import Reg.Support.SingleDependentReadout

/-! The observed pair of parity defects detects saturation of both actual components. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction

noncomputable section

local notation "cubeFlip" =>
  _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip

open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
  (Q flip_apply_same IsBalanced)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (parity)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedGram (maskWeight)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum (maskedGraph)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace (maskedComponentFinset parityDefect)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction (overlapping_mask_xor_intersection)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private mem_maskedComponentFinset eq_off_mask from D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
open private parity_flip flip_ne from D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private abbrev MaskedComponent (I : Finset (Fin 9)) (U : Finset (Q 9)) :=
  ((maskedGraph I).induce (U : Set (Q 9))).ConnectedComponent

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => Bool)

open Classical in
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Finset (Q 9)), IsBalanced U →
    ∀ (I : Finset (Fin 9)) (a b : Fin 9), a ≠ b → I.card = 3 → a ∉ I → b ∉ I →
    ∀ (C : MaskedComponent (insert a I) U) (E : MaskedComponent (insert b I) U)
    (r s : Bool),
    R.readout () ()
      ((parityDefect (maskWeight (insert a I)) (maskedComponentFinset (insert a I) U C) r).det,
       (parityDefect (maskWeight (insert b I)) (maskedComponentFinset (insert b I) U E) s).det) =
      true →
    let F := maskedComponentFinset (insert a I) U C
    let G := maskedComponentFinset (insert b I) U E
    let X := fun t : Bool => F.filter (fun x => cubeFlip (cubeFlip x a) b ∈ G ∧ parity x = t)
    (Disjoint F G → ∀ t, (X t).card ≠ 1) ∧
    ((F ∩ G).Nonempty → (∃ t : Bool, ∀ x ∈ F ∩ G, parity x = t) → ∀ t, (X t).Nonempty)

private def actual : Realization signature :=
  realize signature
    (fun _ _ v => @decide (v = (0, 0)) (Classical.propDecidable _)) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) Empty.elim

set_option maxHeartbeats 500000 in
-- The counterexample uses two actual components of an induced nine-cube.
private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let I : Finset (Fin 9) := {0, 1, 2}
  let a : Fin 9 := 3
  let b : Fin 9 := 4
  have hab : a ≠ b := by decide
  have ha : a ∉ I := by decide
  have hb : b ∉ I := by decide
  let x : Q 9 := fun _ => false
  let y := cubeFlip (cubeFlip x a) b
  have hpar : parity y = parity x := by simp only [y, parity_flip, Bool.not_not]
  have hya : y a = true := by simp [y, flip_ne _ hab, flip_apply_same, x]
  have hyb : y b = true := by simp [y, flip_apply_same, flip_ne _ hab.symm, x]
  have hxy : x ≠ y := by
    intro h
    have hbit := congrFun h a
    rw [hya] at hbit
    exact Bool.noConfusion hbit
  let U : Finset (Q 9) := {x, y}
  have hx : x ∈ U := Finset.mem_insert_self _ _
  have hy : y ∈ U := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huniform : ∀ z ∈ U, parity z = parity x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · simp [h]
    · rw [Finset.mem_singleton.mp h, hpar]
  have hU : IsBalanced U := by
    refine ⟨fun _ => 1, fun _ _ => Or.inl rfl, ?_⟩
    intro u hu v hv hadj
    exact (cubeParity_ne_of_adj hadj ((huniform u hu).trans (huniform v hv).symm)).elim
  let C := ((maskedGraph (insert a I)).induce (U : Set (Q 9))).connectedComponentMk ⟨x, hx⟩
  let E := ((maskedGraph (insert b I)).induce (U : Set (Q 9))).connectedComponentMk ⟨y, hy⟩
  let F := maskedComponentFinset (insert a I) U C
  let G := maskedComponentFinset (insert b I) U E
  have hxF : x ∈ F := (mem_maskedComponentFinset _ U C x).mpr ⟨hx, rfl⟩
  have hyG : y ∈ G := (mem_maskedComponentFinset _ U E y).mpr ⟨hy, rfl⟩
  have hF : F = {x} := by
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hxF)
    intro z hz
    rcases Finset.mem_insert.mp ((mem_maskedComponentFinset _ U C z).mp hz).choose with h | h
    · exact Finset.mem_singleton.mpr h
    · obtain rfl := Finset.mem_singleton.mp h
      have he := eq_off_mask _ U C hz hxF (a := b) (by
        simp [Finset.mem_insert, hab.symm, hb])
      rw [hyb] at he
      exact Bool.noConfusion he
  have hG : G = {y} := by
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hyG)
    intro z hz
    rcases Finset.mem_insert.mp ((mem_maskedComponentFinset _ U E z).mp hz).choose with h | h
    · obtain rfl := h
      have he := eq_off_mask _ U E hz hyG (a := a) (by
        simp [Finset.mem_insert, hab, ha])
      rw [hya] at he
      exact Bool.noConfusion he
    · exact h
  have hdis : Disjoint F G := by simp [hF, hG, hxy]
  have h := (law U hU I a b hab (by decide) ha hb C E (parity x) (parity y) rfl).1 hdis (parity x)
  change (F.filter (fun z => cubeFlip (cubeFlip z a) b ∈ G ∧ parity z = parity x)).card ≠ 1 at h
  apply h
  rw [hF, hG, Finset.filter_singleton]
  rw [ite_eq_left ⟨Finset.mem_singleton_self y, rfl⟩, Finset.card_singleton]

set_option maxHeartbeats 800000 in
-- The bridge compares the complete theorem telescope and both conclusions.
def sourceEvidence : Registration arena (type_of% @overlapping_mask_xor_intersection) where
  actual := actual
  bridge := by simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro U hU I a b hab hI ha hb C E r s h
    exact overlapping_mask_xor_intersection U hU I a b hab hI ha hb C E r s
      (@of_decide_eq_true _ (Classical.propDecidable _) h), rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(), (0, 0), (1, 0), ?_⟩
    simp only [actual, realize, decide_true, decide_false, Prod.mk.injEq, and_true, one_ne_zero]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@overlapping_mask_xor_intersection) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction.overlapping_mask_xor_intersection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ v => @decide (v = (0, 0)) (Classical.propDecidable _)) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/--
info: 'Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction.registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms registration

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction
