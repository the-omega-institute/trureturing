import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage

/-! Source-bound readout of the actual family of trace moments used by the
uniform graph-state coverage classification. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped Classical

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (N : ℕ) → Matrix (Fin N) (Fin N) (ZMod 2) → Finset (Fin N) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ K => physicalMomentFamily K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℝ), 1 < K →
    let observed := R.readout () () K
    (∀ N : ℕ, ∀ A : Matrix (Fin N) (Fin N) (ZMod 2),
      (∀ i j,A i j=A j i) → (∀ i,A i i=0) →
        ∃ p : Word (Fin N) → ℝ, Weight p ∧ ∀ S : Finset (Fin N),
          1 - (∑ U ∈ S.powerset, observed N A U) / (2:ℝ)^S.card = hit S p)
      ↔ ∃ n : ℕ, K = (n:ℝ)+1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 (by norm_num)).mpr ⟨1, by norm_num⟩
  obtain ⟨p,_,hp⟩ := hh 0 0 (fun i j => rfl) (fun i => rfl)
  have he : hit (∅ : Finset (Fin 0)) p = 0 := by
    unfold hit
    apply Finset.sum_eq_zero
    intro x _
    split
    · rfl
    · rename_i hne
      exact (hne (Subsingleton.elim _ _)).elim
  have q := hp ∅
  change (1 : ℝ) - (∑ _ ∈ (∅ : Finset (Fin 0)).powerset, (0 : ℝ)) /
    2^(∅ : Finset (Fin 0)).card = hit ∅ p at q
  simp [he] at q

private def pairGraph : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => if i = j then 0 else 1

private theorem pairGraph_sym (i j : Fin 2) : pairGraph i j = pairGraph j i := by
  simp [pairGraph,eq_comm]

private theorem pairGraph_diag (i : Fin 2) : pairGraph i i = 0 := by simp [pairGraph]


private abbrev left : Finset (Fin 2) := {0}
private abbrev right : Finset (Fin 2) := complement left

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

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(),2,3,?_⟩
  intro h
  have hc := congrFun (congrFun (congrFun h 2) pairGraph) left
  change graphTraceMoment pairGraph 2 left = graphTraceMoment pairGraph 3 left at hc
  rw [(physical_graph_gce_monotone 2 2 pairGraph pairGraph_sym pairGraph_diag (by norm_num)).1,
    (physical_graph_gce_monotone 2 3 pairGraph pairGraph_sym pairGraph_diag (by norm_num)).1,
    rank_pairGraph] at hc
  norm_num [Real.rpow_neg, Real.rpow_natCast] at hc

def source_registration : Registration arena (type_of% @physical_graph_coverage_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_graph_coverage_iff,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_graph_coverage_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage.physical_graph_coverage_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => physicalMomentFamily K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage

/-! Source-bound registration of the full-system Walsh law for the compact
projective graph family, with actual real orders as the state. -/
namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage.Compact
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Classical

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (n : ℕ) → Finset (Fin (2^(n+1))) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ K => compactMomentFamily K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℝ), 1 < K →
    let observed := R.readout () () K
    (∀ n : ℕ, (∑ U : Finset (Fin (2^(n+1))), (-1:ℝ)^U.card * observed n U) =
      2 * ∏ j : Fin (n+1), (1 - (2:ℝ)^j.val / (2:ℝ)^(K-1))) ∧
    (∀ m : ℕ, (2:ℝ)^m < (2:ℝ)^(K-1) → (2:ℝ)^(K-1) < (2:ℝ)^(m+1) →
      ¬ ∃ p : Word (Fin (2^(m+2))) → ℝ, Weight p ∧
        ∀ S : Finset (Fin (2^(m+2))),
        1 - (∑ U ∈ S.powerset, observed (m+1) U) / (2:ℝ)^S.card = hit S p)

private def total (g : signature.Output () ()) : ℝ :=
  ∑ U : Finset (Fin 4), (-1:ℝ)^U.card * g 1 U

private theorem total_two : total (compactMomentFamily 2) = 0 := by
  have e := (compact_projective_characteristic 2 (by norm_num)).1 1
  change total (compactMomentFamily 2) = _ at e
  exact e.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])

private theorem total_three : total (compactMomentFamily 3) = 3/4 := by
  have e := (compact_projective_characteristic 3 (by norm_num)).1 1
  change total (compactMomentFamily 3) = _ at e
  exact e.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have e := (h 3 (by norm_num)).1 1
  change (∑ U : Finset (Fin (2^(1+1))), (-1:ℝ)^U.card * (0:ℝ)) = _ at e
  norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast] at e

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),2,3,?_⟩
  intro he
  have e : total (compactMomentFamily 2) = total (compactMomentFamily 3) := congrArg total he
  rw [total_two,total_three] at e
  norm_num at e

def source_registration : Registration arena (type_of% @compact_projective_characteristic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_projective_characteristic,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_projective_characteristic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage.compact_projective_characteristic.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage.Compact.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => compactMomentFamily K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage.Compact
