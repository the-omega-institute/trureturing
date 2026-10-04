/- GID: D5/S1/Words/GraphRepresentation/UniformVertexExtension
   generality: G
   mirror-B: D5/B/S1/Words/GraphRepresentation/UniformVertexExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extend two uniform actual words by a fresh vertex with any prescribed neighborhood. -/

import D5.S1.Words.GraphRepresentation.ExplicitNonTwoUniform
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Dedup

/-!
The finite carrier `Option V` consists of the old vertices `some a` and the fresh
vertex `none`. Adjacency is equality of the two actual List projections, with
positive uniformity and exact counts over the whole carrier in both words.

The extension is an unbounded structural construction, not a finite-instance
computation, enumeration, certificate checker or numerical reduction. Its utility
classification is `none`. It does not establish adjacent hierarchy strictness.
-/

namespace D5.S1.Words.GraphRepresentation.UniformVertexExtension

open ExplicitNonTwoUniform

/-- Positive-uniform representation by equality of actual two-letter projections. -/
def InG {V : Type*} [DecidableEq V] (k : ℕ) (G : SimpleGraph V) : Prop :=
  0 < k ∧ ∃ w v : List V, (∀ z, w.count z = k) ∧ (∀ z, v.count z = k) ∧
    ∀ a b, a ≠ b → (G.Adj a b ↔ twoProjection a b w = twoProjection a b v)

/-- An arbitrary fresh-vertex neighborhood costs at most one unit of uniformity. -/
theorem vertex_extension {V : Type*} [Finite V] [DecidableEq V]
    (k : ℕ) (G : SimpleGraph (Option V))
    (h : InG k (G.comap Option.some)) : InG (k + 1) G := by
  classical
  let := Fintype.ofFinite V
  let : BEq V := instBEqOfDecidableEq
  let : BEq (Option V) := instBEqOfDecidableEq
  rcases h with ⟨hk, w, v, hw, hv, hadj⟩
  let N := (Finset.univ.filter fun a : V => ¬ G.Adj none (some a)).toList
  let T := (Finset.univ.filter fun a : V => G.Adj none (some a)).toList
  have nc (a : V) : N.count a = if G.Adj none (some a) then 0 else 1 := by
    simp [N, List.Nodup.count, Finset.nodup_toList]
  have tc (a : V) : T.count a = if G.Adj none (some a) then 1 else 0 := by
    simp [T, List.Nodup.count, Finset.nodup_toList]
  let pad : List (Option V) := List.replicate k none
  let W := pad ++ (w.map some ++ (none :: (N ++ T).map some))
  let Z := pad ++ (v.map some ++ (N.map some ++ (none :: T.map some)))
  have old_count (u : List V) (hu : ∀ a, u.count a = k) (a : V) :
      (u.map some).count (some a) = k := by
    simpa only [List.count_map_of_injective _ _ (Option.some_injective V)] using hu a
  have fresh_count (u : List V) : (u.map some).count (none : Option V) = 0 := by
    simp [List.count_eq_zero, List.mem_map]
  have countsW (z : Option V) : W.count z = k + 1 := by
    cases z with
    | none => simp [W, pad, fresh_count]
    | some a =>
      simp [W, pad, List.count_replicate, old_count w hw,
        List.count_map_of_injective _ _ (Option.some_injective V), nc, tc]
      split <;> omega
  have countsZ (z : Option V) : Z.count z = k + 1 := by
    cases z with
    | none => simp [Z, pad, fresh_count]
    | some a =>
      simp [Z, pad, List.count_replicate, old_count v hv,
        List.count_map_of_injective _ _ (Option.some_injective V), nc, tc]
      split <;> omega
  have oldW (a b : V) :
      twoProjection (some a) (some b) W =
        (twoProjection a b w ++ twoProjection a b (N ++ T)).map some := by
    simp [W, pad, twoProjection, List.filter_map, Function.comp_def, Bool.beq_eq_decide_eq,
      List.map_append]
  have oldZ (a b : V) :
      twoProjection (some a) (some b) Z =
        (twoProjection a b v ++ twoProjection a b (N ++ T)).map some := by
    simp [Z, pad, twoProjection, List.filter_map, Function.comp_def, Bool.beq_eq_decide_eq,
      List.map_append]
  have freshW (a : V) :
      twoProjection none (some a) W =
        pad ++ (List.replicate k (some a) ++ [none, some a]) := by
    by_cases ha : G.Adj none (some a) <;>
      simp [W, pad, twoProjection, List.filter_map, Function.comp_def, Bool.beq_eq_decide_eq,
        List.filter_eq, hw, nc, tc, ha]
  have fresh_edge (a : V) :
      G.Adj none (some a) ↔ twoProjection none (some a) W =
        twoProjection none (some a) Z := by
    rw [freshW]
    by_cases ha : G.Adj none (some a)
    · simp [Z, pad, twoProjection, List.filter_map, Function.comp_def, Bool.beq_eq_decide_eq,
        List.filter_eq, hv, nc, tc, ha]
    · simp [Z, pad, twoProjection, List.filter_map, Function.comp_def, Bool.beq_eq_decide_eq,
        List.filter_eq, hv, nc, tc, ha]
  refine ⟨by omega, W, Z, countsW, countsZ, ?_⟩
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some b => exact fresh_edge b
  | some a =>
    cases b with
    | none =>
      simpa only [SimpleGraph.adj_comm, twoProjection, Bool.or_comm]
        using fresh_edge a
    | some b =>
      rw [oldW, oldZ, List.map_inj_right (Option.some_injective V),
        List.append_left_inj]
      exact hadj a b (fun heq => hab (congrArg some heq))

end D5.S1.Words.GraphRepresentation.UniformVertexExtension
