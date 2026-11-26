import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

/-! Source-bound readout of the original graph-state reduction's real trace moment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped Classical

noncomputable section

abbrev signature : Signature where
  Params := Sigma (fun _ : ℕ => ℝ)
  State p := Matrix (Fin p.1) (Fin p.1) (ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Fin p.1) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p A => graphTraceMoment A p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (K : ℝ) (A : Matrix (Fin N) (Fin N) (ZMod 2)),
    (∀ i j, A i j = A j i) → (∀ i, A i i = 0) → 1 < K →
    let observed := R.readout () ⟨N,K⟩ A
    (∀ U, observed U = (2 : ℝ) ^ ((1 - K) * cutRank A U)) ∧
      Monotone (fromTraceMoments K observed)

private def pairGraph : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => if i = j then 0 else 1

private theorem pairGraph_sym (i j : Fin 2) : pairGraph i j = pairGraph j i := by
  simp [pairGraph,eq_comm]

private theorem pairGraph_diag (i : Fin 2) : pairGraph i i = 0 := by simp [pairGraph]


private abbrev left : Finset (Fin 2) := {0}
private abbrev right : Finset (Fin 2) := complement left

private theorem rank_emptyGraph : cutRank (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) left = 0 := by
  unfold cutRank cutMatrix
  exact Matrix.rank_zero

private theorem rank_pairGraph : cutRank pairGraph left = 1 := by
  let B := cutMatrix pairGraph left right
  unfold cutRank
  change B.rank = 1
  let u : left := ⟨0,by simp⟩
  let v : right := ⟨1,by simp [right,complement]⟩
  have hl (j : left) : j = u := by
    apply Subtype.ext
    exact Finset.mem_singleton.mp j.property
  have hr (i : right) : i = v := by
    apply Subtype.ext
    have hi : i.val ≠ 0 := by simpa [right,complement] using i.property
    have hj : i.val = 1 := by
      revert hi
      generalize i.val = j
      decide +kernel +revert
    simpa [v] using hj
  have hv : Fintype.card right = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    exact ⟨v,hr⟩
  have hsurj : Function.Surjective (Matrix.mulVec B) := by
    intro z
    refine ⟨fun _ => z v,?_⟩
    funext i
    rw [hr i]
    change (∑ j : left, B v j * z v) = z v
    rw [Finset.sum_eq_single u]
    · simp [B,cutMatrix,pairGraph,u,v]
    · intro j _ hj
      exact (hj (hl j)).elim
    · exact fun h => (h (Finset.mem_univ u)).elim
  simpa only [hv] using (Matrix.mulVec_surjective_iff_rank_eq_card.mp hsurj)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 2 0 (fun i j => rfl) (fun i => rfl) (by norm_num)).1 left
  change (0 : ℝ) = 2 ^ ((1 - 2) * (cutRank
    (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) left : ℝ)) at hh
  norm_num [rank_emptyGraph] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2,2⟩,0,pairGraph,?_⟩
  intro h
  have hc := congrFun h left
  change graphTraceMoment (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 2 left =
    graphTraceMoment pairGraph 2 left at hc
  rw [(physical_graph_gce_monotone 2 2 0 (fun i j => rfl) (fun i => rfl) (by norm_num)).1,
    (physical_graph_gce_monotone 2 2 pairGraph pairGraph_sym pairGraph_diag (by norm_num)).1,
    rank_emptyGraph,rank_pairGraph] at hc
  norm_num [Real.rpow_neg] at hc

def source_registration : Registration arena (type_of% @physical_graph_gce_monotone) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_graph_gce_monotone,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_graph_gce_monotone) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement.physical_graph_gce_monotone.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p A => graphTraceMoment A p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","value"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
