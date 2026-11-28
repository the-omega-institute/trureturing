/- GID: D5/S3/Combinatorics/Graph/Sunlet/DetourPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Sunlet/DetourPath
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Longest simple paths in a sunlet use the longer of its two cycle arcs. -/

module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import OmegaBuild.Commands
import Mathlib.Algebra.Group.Fin.Basic

/-! The longest simple path between distinct cycle indices of a sunlet. -/

compile_only_with_mathlib

@[expose] public section

namespace AlsinaiAhmed.Sunlet

open SimpleGraph SimpleGraph.Walk
open scoped Fin.NatCast

/-- A cycle with one leaf at each vertex. Height zero is on the cycle. -/
def sunlet (n : ℕ) : SimpleGraph (Fin n × Fin 2) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.2 = 0 ∧ y.2 = 0 ∧ (cycleGraph n).Adj x.1 y.1)
  symm.symm := by
    rintro x y (⟨h, h'⟩ | ⟨hx, hy, h⟩)
    · exact Or.inl ⟨h.symm, h'.symm⟩
    · exact Or.inr ⟨hy, hx, h.symm⟩
  loopless.irrefl := by simp

private theorem cycle_step {n : ℕ} {x y : Fin (n + 3)}
    (h : (cycleGraph (n + 3)).Adj x y) : y = x + 1 ∨ x = y + 1 := by
  rcases cycleGraph_adj.mp h with h | h
  · exact Or.inr (sub_eq_iff_eq_add'.mp h)
  · exact Or.inl (sub_eq_iff_eq_add'.mp h)

private theorem directed_step {n : ℕ} {x y d : Fin (n + 3)}
    (hd : d = 1 ∨ d = -1) (h : (cycleGraph (n + 3)).Adj x y) :
    y = x + d ∨ x = y + d := by
  rcases hd with rfl | rfl
  · exact cycle_step h
  · rcases cycle_step h with h | h
    · right
      simpa [add_assoc] using (congrArg (· + (-1 : Fin (n + 3))) h).symm
    · left
      simpa [add_assoc] using (congrArg (· + (-1 : Fin (n + 3))) h).symm

private theorem oriented_end {n : ℕ} {x y d : Fin (n + 3)}
    (hd : d = 1 ∨ d = -1) (p : (cycleGraph (n + 3)).Walk x y)
    (hp : p.IsPath) (previous : Fin (n + 3))
    (hprev : x = previous + d) (hfresh : previous ∉ p.support) :
    y = x + p.length • d := by
  induction p generalizing previous with
  | nil => simp
  | @cons x z y h p ih =>
    have hx : x ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
    have hz : z = x + d := by
      rcases directed_step hd h with hz | hz
      · exact hz
      · have he : previous = z := add_right_cancel (hprev.symm.trans hz)
        exact (hfresh (by simp [he])).elim
    calc
      y = z + p.length • d := ih hp.of_cons x hz hx
      _ = (x + d) + p.length • d := congrArg (· + p.length • d) hz
      _ = x + (cons h p).length • d := by rw [length_cons, succ_nsmul]; ac_rfl

private theorem arc_length {n : ℕ} {i j : Fin (n + 3)}
    (p : (cycleGraph (n + 3)).Walk i j) (hp : p.IsPath) :
    p.length = (i - j).val ∨ p.length = (j - i).val := by
  have hlt : p.length < n + 3 := by simpa using hp.length_lt
  have hEnd : ∃ d : Fin (n + 3), (d = 1 ∨ d = -1) ∧ j = i + p.length • d := by
    cases p with
    | nil => exact ⟨1, Or.inl rfl, by simp⟩
    | @cons i z j h p =>
      have hf : i ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
      rcases cycle_step h with hz | hi
      · refine ⟨1, Or.inl rfl, ?_⟩
        calc
          j = z + p.length • (1 : Fin (n + 3)) := oriented_end (Or.inl rfl) p hp.of_cons i hz hf
          _ = (i + 1) + p.length • (1 : Fin (n + 3)) :=
            congrArg (· + p.length • (1 : Fin (n + 3))) hz
          _ = i + (cons h p).length • (1 : Fin (n + 3)) := by rw [length_cons, succ_nsmul]; ac_rfl
      · have hz : z = i + (-1 : Fin (n + 3)) := by
          simpa [add_assoc] using (congrArg (· + (-1 : Fin (n + 3))) hi).symm
        refine ⟨-1, Or.inr rfl, ?_⟩
        calc
          j = z + p.length • (-1 : Fin (n + 3)) := oriented_end (Or.inr rfl) p hp.of_cons i hz hf
          _ = (i + -1) + p.length • (-1 : Fin (n + 3)) :=
            congrArg (· + p.length • (-1 : Fin (n + 3))) hz
          _ = i + (cons h p).length • (-1 : Fin (n + 3)) := by rw [length_cons, succ_nsmul]; ac_rfl
  obtain ⟨d, rfl | rfl, he⟩ := hEnd
  · right
    have h : j - i = (p.length : Fin (n + 3)) := by
      calc
        j - i = (i + p.length • (1 : Fin (n + 3))) - i := congrArg (· - i) he
        _ = (p.length : Fin (n + 3)) := by simp
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt hlt] using (congrArg Fin.val h).symm
  · left
    have h : i - j = (p.length : Fin (n + 3)) := by
      calc
        i - j = i - (i + p.length • (-1 : Fin (n + 3))) := congrArg (i - ·) he
        _ = (p.length : Fin (n + 3)) := by simp [← sub_eq_add_neg]
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt hlt] using (congrArg Fin.val h).symm

private def cycleTranslate {n : ℕ} (i : Fin (n + 3)) :
    cycleGraph (n + 3) →g cycleGraph (n + 3) where
  toFun x := i + x
  map_rel' := by
    intro x y h
    rw [cycleGraph_adj] at h ⊢
    simpa using h

private theorem backward_arc {n : ℕ} (i j : Fin (n + 3)) :
    ∃ p : (cycleGraph (n + 3)).Walk i j, p.IsPath ∧ p.length = (i - j).val := by
  let k := (i - j).val
  have hk : k < n + 3 := (i - j).isLt
  let p := (cycleGraph.cycle n).take k
  have hEnd : (cycleTranslate i) ((cycleGraph.cycle n).getVert k) = j := by
    change i + (cycleGraph.cycle n).getVert k = j
    rw [cycleGraph.getVert_cycle hk.le]
    have hneg : (⟨(n + 3 - k) % (n + 3), Nat.mod_lt _ (by omega)⟩ :
        Fin (n + 3)) = -(i - j) := by
      apply Fin.ext
      rfl
    rw [hneg, ← sub_eq_add_neg, sub_sub_cancel]
  have hStart : cycleTranslate i 0 = i := by
    change i + 0 = i
    simp
  refine ⟨(p.map (cycleTranslate i)).copy hStart hEnd, ?_, ?_⟩
  · rw [isPath_copy]
    have hinj : Function.Injective (cycleTranslate i) := fun _ _ h ↦ add_left_cancel h
    exact ((cycleGraph.isCycle_cycle (n := n)).isPath_take (by simpa using hk)).map hinj
  · simp [p, take_length, k]

private def cycleCore (n : ℕ) : cycleGraph n →g sunlet n where
  toFun i := (i, 0)
  map_rel' h := Or.inr ⟨rfl, rfl, h⟩

private theorem neighbor_of_leaf {n : ℕ} {i : Fin n} {x : Fin n × Fin 2}
    (h : (sunlet n).Adj (i, 1) x) : x = (i, 0) := by
  rcases h with ⟨hi, hh⟩ | ⟨hh, _, _⟩
  · have : ∀ a : Fin 2, 1 ≠ a → a = 0 := by decide
    exact Prod.ext hi.symm (this x.2 hh)
  · exact (by decide : (1 : Fin 2) ≠ 0) hh |>.elim

private theorem core_adj {n : ℕ} {i j : Fin n}
    (h : (sunlet n).Adj (i, 0) (j, 0)) : (cycleGraph n).Adj i j := by
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩
  · exact (h rfl).elim
  · exact h

private theorem fin_two (a : Fin 2) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ a : Fin 2, a = 0 ∨ a = 1) a

private theorem trim_start {n : ℕ} {i j : Fin n} {a b : Fin 2} (hij : i ≠ j)
    (p : (sunlet n).Walk (i, a) (j, b)) (hp : p.IsPath) :
    ∃ q : (sunlet n).Walk (i, 0) (j, b), q.IsPath ∧ p.length = q.length + a.val := by
  obtain rfl | rfl := fin_two a
  · exact ⟨p, hp, by simp⟩
  · cases p with
    | nil => exact (hij rfl).elim
    | @cons _ x _ h p =>
      have he := neighbor_of_leaf h
      subst x
      exact ⟨p, hp.of_cons, by rfl⟩

private theorem cycle_of_core_path {n : ℕ} {x y : Fin n × Fin 2}
    (p : (sunlet n).Walk x y) (hp : p.IsPath) (hx : x.2 = 0) (hy : y.2 = 0) :
    ∃ q : (cycleGraph n).Walk x.1 y.1, q.IsPath ∧ q.length = p.length ∧
      q.support.map (cycleCore n) = p.support := by
  induction p with
  | @nil x =>
    refine ⟨nil, IsPath.nil, rfl, ?_⟩
    change [(x.1, 0)] = [x]
    rw [show (x.1, 0) = x from Prod.ext rfl hx.symm]
  | @cons x z y h p ih =>
    have hz : z.2 = 0 := by
      rcases fin_two z.2 with hz | hz
      · exact hz
      · exfalso
        have hz' : z = (z.1, 1) := Prod.ext rfl hz
        have hxf : x ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
        cases p with
        | nil => rw [hy] at hz; exact (by decide : (0 : Fin 2) ≠ 1) hz
        | @cons _ w _ h' p' =>
          rw [hz'] at h h'
          have he := (neighbor_of_leaf h.symm).trans (neighbor_of_leaf h').symm
          exact hxf (by simp [he])
    have hc : (cycleGraph n).Adj x.1 z.1 := by
      have hx' : x = (x.1, 0) := Prod.ext rfl hx
      have hz' : z = (z.1, 0) := Prod.ext rfl hz
      exact core_adj (hx' ▸ hz' ▸ h)
    obtain ⟨q, hq, hlen, hs⟩ := ih hp.of_cons hz hy
    have hxq : x.1 ∉ q.support := by
      intro hm
      have hxf : x ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
      apply hxf
      rw [← hs, List.mem_map]
      exact ⟨x.1, hm, Prod.ext rfl hx.symm⟩
    refine ⟨cons hc q, IsPath.mk' (List.nodup_cons.mpr ⟨hxq, hq.support_nodup⟩), ?_, ?_⟩
    · simp [hlen]
    · simp only [support_cons, List.map_cons, hs]
      rw [show cycleCore n x.1 = x from Prod.ext rfl hx.symm]


private theorem has_cycle_path {n : ℕ} {i j : Fin n} {a b : Fin 2} (hij : i ≠ j)
    (p : (sunlet n).Walk (i, a) (j, b)) (hp : p.IsPath) :
    ∃ q : (cycleGraph n).Walk i j, q.IsPath ∧ p.length = q.length + a.val + b.val := by
  obtain ⟨s, hs, ha⟩ := trim_start hij p hp
  obtain ⟨t, ht, hb⟩ := trim_start hij.symm s.reverse hs.reverse
  obtain ⟨q, hq, hlen, _⟩ := cycle_of_core_path t.reverse ht.reverse rfl rfl
  refine ⟨q, hq, ?_⟩
  rw [length_reverse] at hb hlen
  omega

private theorem core_to_leaf_adj {n : ℕ} (i : Fin n) :
    (sunlet n).Adj (i, 0) (i, 1) :=
  Or.inl ⟨rfl, by change (0 : Fin 2) ≠ 1; decide⟩

private theorem extend_cycle_path {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a b : Fin 2)
    (q : (cycleGraph n).Walk i j) (hq : q.IsPath) :
    ∃ p : (sunlet n).Walk (i, a) (j, b), p.IsPath ∧ p.length = q.length + a.val + b.val := by
  let core : (sunlet n).Walk (i, 0) (j, 0) := q.map (cycleCore n)
  have hc : core.IsPath := hq.map (fun _ _ h ↦ congrArg Prod.fst h)
  have hCoreLen : core.length = q.length := Walk.length_map (cycleCore n) q
  have noLeaf (k : Fin n) : (k, 1) ∉ core.support := by
    intro hm
    change (k, 1) ∈ (q.map (cycleCore n)).support at hm
    rw [Walk.support_map, List.mem_map] at hm
    obtain ⟨x, _, hx⟩ := hm
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd hx)
  have endLift : ∃ s : (sunlet n).Walk (i, 0) (j, b), s.IsPath ∧
      s.length = q.length + b.val ∧ (i, 1) ∉ s.support := by
    obtain rfl | rfl := fin_two b
    · exact ⟨core, hc, by simpa using hCoreLen, noLeaf i⟩
    · refine ⟨core.concat (core_to_leaf_adj j), hc.concat (noLeaf j) _, ?_, ?_⟩
      · calc
          (core.concat (core_to_leaf_adj j)).length = core.length + 1 :=
            Walk.length_concat core (core_to_leaf_adj j)
          _ = q.length + (1 : Fin 2).val := by rw [hCoreLen]; rfl
      · rw [support_concat, List.mem_append]
        simp [noLeaf i, hij]
  obtain ⟨s, hs, hl, hf⟩ := endLift
  obtain rfl | rfl := fin_two a
  · exact ⟨s, hs, by simpa using hl⟩
  · refine ⟨cons (core_to_leaf_adj i).symm s, hs.cons hf, ?_⟩
    rw [length_cons, hl]
    omega

/-- Between distinct indices, the longest simple path uses the longer cycle arc
and the leaf edge at each leaf endpoint. -/
theorem sunlet_isGreatest_pathLength_of_index_ne {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j) (a b : Fin 2) :
    IsGreatest {L : ℕ | ∃ p : (sunlet n).Walk (i, a) (j, b), p.IsPath ∧ p.length = L}
      (max (i - j).val (j - i).val + a.val + b.val) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  constructor
  · have hArc : ∃ q : (cycleGraph (m + 3)).Walk i j, q.IsPath ∧
        q.length = max (i - j).val (j - i).val := by
      by_cases h : (j - i).val ≤ (i - j).val
      · rw [max_eq_left h]
        exact backward_arc i j
      · rw [max_eq_right (by omega)]
        obtain ⟨q, hq, hl⟩ := backward_arc j i
        exact ⟨q.reverse, hq.reverse, by simpa using hl⟩
    obtain ⟨q, hq, hl⟩ := hArc
    obtain ⟨p, hp, hlen⟩ := extend_cycle_path hij a b q hq
    exact ⟨p, hp, by rw [hlen, hl]⟩
  · rintro L ⟨p, hp, hL⟩
    obtain ⟨q, hq, hlen⟩ := has_cycle_path hij p hp
    have hle : q.length ≤ max (i - j).val (j - i).val := by
      obtain h | h := arc_length q hq
      · rw [h]; exact le_max_left _ _
      · rw [h]; exact le_max_right _ _
    change L ≤ _
    omega

#print axioms sunlet_isGreatest_pathLength_of_index_ne

end AlsinaiAhmed.Sunlet
