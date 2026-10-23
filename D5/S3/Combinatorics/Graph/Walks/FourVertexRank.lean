/- GID: D5/S3/Combinatorics/Graph/Walks/FourVertexRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/FourVertexRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching, mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Structural counts of actual four-vertex perfect-matching subgraphs. -/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000
open SimpleGraph Matrix
open scoped Classical
namespace D5.S3.Combinatorics.Graph.Walks.FourVertexRank
noncomputable section

def mate (j : Fin 3) : Fin 4 → Fin 4 :=
  ![![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] j

def pmCount (H : SimpleGraph (Fin 4)) : ℕ :=
  Nat.card {M : H.Subgraph // M.IsPerfectMatching}

/-- Identifies actual perfect-matching subgraphs with the supported pairings and counts them. -/
theorem actual_matching_count (H : SimpleGraph (Fin 4)) :
    (∀ M : H.Subgraph, M.IsPerfectMatching ↔
      ∃ j : Fin 3, (∀ i, H.Adj i (mate j i)) ∧
        ∀ i k, M.Adj i k ↔ mate j i = k) ∧
    pmCount H = (if H.Adj 0 1 ∧ H.Adj 2 3 then 1 else 0) +
      (if H.Adj 0 2 ∧ H.Adj 1 3 then 1 else 0) +
      (if H.Adj 0 3 ∧ H.Adj 1 2 then 1 else 0) := by
  classical
  let J := {j : Fin 3 // ∀ i, H.Adj i (mate j i)}
  have invol (j : Fin 3) : Function.Involutive (mate j) := by
    intro i
    fin_cases j <;> fin_cases i <;> rfl
  let build (j : J) : H.Subgraph := {
    verts := Set.univ
    Adj i k := mate j i = k
    adj_sub := by intro i k h; exact h ▸ j.property i
    edge_vert := by intro i k h; trivial
    symm := ⟨by intro i k h; rw [← h]; exact invol j i⟩ }
  have perfect (j : J) : (build j).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro i
    exact ⟨mate j i, rfl, fun k hk => (show mate j i = k from hk).symm⟩
  let f : J → {M : H.Subgraph // M.IsPerfectMatching} := fun j => ⟨build j, perfect j⟩
  have inj : Function.Injective f := by
    intro j k h
    have he : mate k 0 = mate j 0 := by
      have hM := congrArg Subtype.val h
      have ha : (build j).Adj 0 (mate j 0) := rfl
      change build j = build k at hM
      rw [hM] at ha
      exact ha
    apply Subtype.ext
    rcases j with ⟨j, hj⟩
    rcases k with ⟨k, hk⟩
    fin_cases j <;> fin_cases k <;> simp [mate] at he ⊢
  have surj : Function.Surjective f := by
    intro M
    obtain ⟨w, hw, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property 0
    have wn : w ≠ 0 := (H.ne_of_adj (M.val.adj_sub hw)).symm
    have uniq := M.property.1
    have force (j : Fin 3) (hj : mate j 0 = w) :
        ∀ i k, M.val.Adj i k ↔ mate j i = k := by
      have h0 : M.val.Adj 0 (mate j 0) := hj.symm ▸ hw
      have all (i : Fin 4) : M.val.Adj i (mate j i) := by
        fin_cases j
        · have h01 : M.val.Adj 0 1 := h0
          obtain ⟨z, hz, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property 2
          have zne : z ≠ 2 := (H.ne_of_adj (M.val.adj_sub hz)).symm
          have zn0 : z ≠ 0 := by
            intro h; subst z
            have h := uniq.eq_of_adj_left hz.symm h01
            omega
          have zn1 : z ≠ 1 := by
            intro h; subst z
            have h := uniq.eq_of_adj_left hz.symm h01.symm
            omega
          have ze : z = 3 := by omega
          subst z
          fin_cases i <;> simp [mate] <;> first | exact h01 | exact h01.symm | exact hz | exact hz.symm
        · have h02 : M.val.Adj 0 2 := h0
          obtain ⟨z, hz, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property 1
          have zne : z ≠ 1 := (H.ne_of_adj (M.val.adj_sub hz)).symm
          have zn0 : z ≠ 0 := by
            intro h; subst z
            have h := uniq.eq_of_adj_left hz.symm h02
            omega
          have zn2 : z ≠ 2 := by
            intro h; subst z
            have h := uniq.eq_of_adj_left hz.symm h02.symm
            omega
          have ze : z = 3 := by omega
          subst z
          fin_cases i <;> simp [mate] <;> first | exact h02 | exact h02.symm | exact hz | exact hz.symm
        · have h03 : M.val.Adj 0 3 := h0
          obtain ⟨z, hz, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property 1
          have zne : z ≠ 1 := (H.ne_of_adj (M.val.adj_sub hz)).symm
          have zn0 : z ≠ 0 := by
            intro h; subst z
            have h := uniq.eq_of_adj_left hz.symm h03
            omega
          have zn3 : z ≠ 3 := by
            intro h; subst z
            have h := uniq.eq_of_adj_left hz.symm h03.symm
            omega
          have ze : z = 2 := by omega
          subst z
          fin_cases i <;> simp [mate] <;> first | exact h03 | exact h03.symm | exact hz | exact hz.symm
      intro i k
      exact ⟨fun h => (uniq.eq_of_adj_left (all i) h), fun h => h ▸ all i⟩
    have jw : ∃ j : Fin 3, mate j 0 = w := by
      fin_cases w <;> simp [mate] at *
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨j, hj⟩ := jw
    let jj : J := ⟨j, fun i => M.val.adj_sub ((force j hj i (mate j i)).mpr rfl)⟩
    refine ⟨jj, ?_⟩
    apply Subtype.ext
    change build jj = M.val
    apply Subgraph.ext (by change Set.univ = M.val.verts; exact M.property.2.verts_eq_univ.symm)
    funext i k
    exact propext (force j hj i k).symm
  constructor
  · intro M
    constructor
    · intro hM
      obtain ⟨j, hj⟩ := surj ⟨M, hM⟩
      refine ⟨j.val, j.property, ?_⟩
      have hv := congrArg Subtype.val hj
      change build j = M at hv
      intro i k
      rw [← hv]
    · rintro ⟨j, _, hj⟩
      rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
      intro i
      exact ⟨mate j i, (hj i (mate j i)).mpr rfl,
        fun k hk => ((hj i k).mp hk).symm⟩
  · have card := Fintype.card_of_bijective (f := f) ⟨inj, surj⟩
    have hc : pmCount H = Fintype.card J := by
      rw [pmCount, Nat.card_eq_fintype_card]
      exact card.symm
    rw [hc, Fintype.card_subtype]
    rw [Finset.card_filter]
    simp only [Fin.sum_univ_succ]
    have hs (j : Fin 3) : (∀ i, H.Adj i (mate j i)) ↔
        (j = 0 ∧ H.Adj 0 1 ∧ H.Adj 2 3) ∨
        (j = 1 ∧ H.Adj 0 2 ∧ H.Adj 1 3) ∨
        (j = 2 ∧ H.Adj 0 3 ∧ H.Adj 1 2) := by
      fin_cases j <;> simp [mate, Fin.forall_fin_succ] <;>
        aesop (add safe forward SimpleGraph.Adj.symm)
    simp [hs, add_assoc]

#print axioms actual_matching_count
end
end D5.S3.Combinatorics.Graph.Walks.FourVertexRank
