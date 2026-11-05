/- GID: D5/S3/Combinatorics/Graph/Jacobi/LeafPruningExistence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/LeafPruningExistence
   mirror-E: none(waiver:actual-finite-terminal-leaf-pruning)
   anchors: []
   utility: none
   digest: Every finite actual flag graph admits a terminal anchor-protected leaf pruning. -/

import D5.S3.Combinatorics.Graph.Jacobi.FlagPruning
import Mathlib.Data.Nat.Find

/-! Maximal finite deletion prefixes yield genuine terminal leaf prunings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi.FlagGraph

private structure PruningPrefix {F : Type} [Finite F] (G : FlagGraph F) where
  steps : ℕ
  rank : G.VertexOrbit → ℕ
  rank_le : ∀ v, rank v ≤ steps
  rank_injective : ∀ v w, rank v < steps → rank w < steps → rank v = rank w → v = w
  each_step : ∀ i, i < steps → ∃ v, rank v = i
  protect_anchor : ∀ v, G.HasAnchor v → rank v = steps
  deletion_degree : ∀ v, rank v < steps →
    Nat.card {f : F // G.vertexOf f = v ∧ rank v ≤ rank (G.vertexOf (G.edge f))} ≤ 1

namespace PruningPrefix

private def zero {F : Type} [Finite F] (G : FlagGraph F) : PruningPrefix G where
  steps := 0
  rank _ := 0
  rank_le _ := le_rfl
  rank_injective := by intro v w hv; omega
  each_step := by intro i hi; omega
  protect_anchor := by intro v h; rfl
  deletion_degree := by intro v hv; omega

private theorem steps_le_card {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) : P.steps ≤ Nat.card G.VertexOrbit := by
  let f : Fin P.steps → G.VertexOrbit := fun i => (P.each_step i i.isLt).choose
  have hf (i : Fin P.steps) : P.rank (f i) = i := (P.each_step i i.isLt).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact (hf i).symm.trans ((congrArg P.rank hij).trans (hf j))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hinj

private noncomputable def nextRank {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v w : G.VertexOrbit) : ℕ := by
  classical
  exact if w = v then P.steps else if P.rank w = P.steps then P.steps + 1 else P.rank w

private theorem nextRank_at {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) : P.nextRank v v = P.steps := by
  simp [nextRank]

private theorem nextRank_old {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) (hv : P.rank v = P.steps)
    (w : G.VertexOrbit) (hw : P.rank w < P.steps) : P.nextRank v w = P.rank w := by
  classical
  have hwv : w ≠ v := by intro h; subst w; omega
  simp [nextRank, hwv, ne_of_lt hw]

private theorem nextRank_bound {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) (hv : P.rank v = P.steps)
    (w : G.VertexOrbit) : P.rank w ≤ P.nextRank v w ∧ P.nextRank v w ≤ P.steps + 1 := by
  classical
  have hw := P.rank_le w
  by_cases hwv : w = v
  · subst w; simp only [nextRank_at, hv]; omega
  · by_cases hwt : P.rank w = P.steps <;>
      simp only [nextRank, ite_eq_right hwv, hwt, ↓reduceIte] <;> omega

private theorem nextRank_deleted {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) (_hv : P.rank v = P.steps)
    (w : G.VertexOrbit) : P.nextRank v w < P.steps + 1 ↔ P.rank w < P.steps ∨ w = v := by
  classical
  have hw := P.rank_le w
  by_cases hwv : w = v
  · subst w; simp [nextRank]
  · by_cases hwt : P.rank w = P.steps <;>
      simp only [nextRank, hwt, ↓reduceIte, hwv, or_false] <;> omega

private theorem nextRank_terminal {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) (hv : P.rank v = P.steps)
    (w : G.VertexOrbit) : P.steps ≤ P.nextRank v w ↔ P.rank w = P.steps := by
  classical
  have hw := P.rank_le w
  by_cases hlt : P.rank w < P.steps
  · rw [P.nextRank_old v hv w hlt]
    omega
  · have hb := (P.nextRank_bound v hv w).1
    omega

private theorem nextRank_old_compare {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) (hv : P.rank v = P.steps)
    (w : G.VertexOrbit) (hw : P.rank w < P.steps) (t : G.VertexOrbit) :
    P.nextRank v w ≤ P.nextRank v t ↔ P.rank w ≤ P.rank t := by
  rw [P.nextRank_old v hv w hw]
  by_cases ht : P.rank t = P.steps
  · have hb := (P.nextRank_bound v hv t).1; omega
  · have hb := P.rank_le t
    have htl : P.rank t < P.steps := by omega
    rw [P.nextRank_old v hv t htl]

private noncomputable def extend {F : Type} [Finite F] {G : FlagGraph F}
    (P : PruningPrefix G) (v : G.VertexOrbit) (hv : P.rank v = P.steps)
    (ha : ¬G.HasAnchor v)
    (hd : Nat.card {f : F // G.vertexOf f = v ∧ P.rank (G.vertexOf (G.edge f)) = P.steps} ≤ 1) :
    PruningPrefix G where
  steps := P.steps + 1
  rank := P.nextRank v
  rank_le w := (P.nextRank_bound v hv w).2
  rank_injective := by
    classical
    intro a b ha' hb' hab
    by_cases hav : a = v
    · subst a
      by_cases hbv : b = v
      · exact hbv.symm
      · have hbo := ((P.nextRank_deleted v hv b).mp hb').resolve_right hbv
        rw [P.nextRank_at, P.nextRank_old v hv b hbo] at hab
        omega
    · by_cases hbv : b = v
      · subst b
        have hao := ((P.nextRank_deleted v hv a).mp ha').resolve_right hav
        rw [P.nextRank_old v hv a hao, P.nextRank_at] at hab
        omega
      · have hao := ((P.nextRank_deleted v hv a).mp ha').resolve_right hav
        have hbo := ((P.nextRank_deleted v hv b).mp hb').resolve_right hbv
        apply P.rank_injective a b hao hbo
        simpa only [P.nextRank_old v hv a hao, P.nextRank_old v hv b hbo] using hab
  each_step := by
    classical
    intro i hi
    by_cases hi' : i < P.steps
    · obtain ⟨w, hw⟩ := P.each_step i hi'
      refine ⟨w, ?_⟩
      rw [P.nextRank_old v hv w (by omega), hw]
    · have he : i = P.steps := by omega
      exact ⟨v, (P.nextRank_at v).trans he.symm⟩
  protect_anchor := by
    classical
    intro w hw
    have hwv : w ≠ v := by intro h; subst w; exact ha hw
    simp only [nextRank, ite_eq_right hwv, P.protect_anchor w hw, ↓reduceIte]
  deletion_degree := by
    classical
    intro w hw
    by_cases hwv : w = v
    · subst w
      have hcard :
          Nat.card {f : F // G.vertexOf f = v ∧ P.nextRank v v ≤ P.nextRank v (G.vertexOf (G.edge f))} =
            Nat.card {f : F // G.vertexOf f = v ∧ P.rank (G.vertexOf (G.edge f)) = P.steps} := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun f => by
          rw [P.nextRank_at, P.nextRank_terminal v hv])
      rw [hcard]
      exact hd
    · have hwo := ((P.nextRank_deleted v hv w).mp hw).resolve_right hwv
      have hcard :
          Nat.card {f : F // G.vertexOf f = w ∧ P.nextRank v w ≤ P.nextRank v (G.vertexOf (G.edge f))} =
            Nat.card {f : F // G.vertexOf f = w ∧ P.rank w ≤ P.rank (G.vertexOf (G.edge f))} := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun f => by rw [P.nextRank_old_compare v hv w hwo])
      rw [hcard]
      exact P.deletion_degree w hwo

end PruningPrefix

/-- Every finite original flag graph admits a genuine terminal leaf-pruning
chronology protecting every numbered anchor. Loops retain both actual flags. -/
theorem exists_leaf_pruning {F : Type} [Finite F] (G : FlagGraph F) :
    Nonempty G.LeafPruning := by
  classical
  let pred : ℕ → Prop := fun n => ∃ P : PruningPrefix G, P.steps = n
  have hzero : pred 0 := ⟨PruningPrefix.zero G, rfl⟩
  let k := Nat.findGreatest pred (Nat.card G.VertexOrbit)
  have hk : pred k := Nat.findGreatest_spec (Nat.zero_le _) hzero
  obtain ⟨P, hP⟩ := hk
  refine ⟨{
    steps := P.steps
    rank := P.rank
    rank_le := P.rank_le
    rank_injective := P.rank_injective
    each_step := P.each_step
    protect_anchor := P.protect_anchor
    deletion_degree := P.deletion_degree
    terminal_degree := ?_ }⟩
  intro v hv ha
  by_contra h
  have hd : Nat.card {f : F //
      G.vertexOf f = v ∧ P.rank (G.vertexOf (G.edge f)) = P.steps} ≤ 1 := by omega
  let Q := P.extend v hv ha hd
  have hQ : pred (P.steps + 1) := ⟨Q, rfl⟩
  have hb : P.steps + 1 ≤ Nat.card G.VertexOrbit := Q.steps_le_card
  have hm : P.steps + 1 ≤ k := Nat.le_findGreatest hb hQ
  omega

end D5.S3.Combinatorics.Graph.Jacobi.FlagGraph
