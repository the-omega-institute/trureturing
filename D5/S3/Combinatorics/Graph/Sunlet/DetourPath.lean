/- GID: D5/S3/Combinatorics/Graph/Sunlet/DetourPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Sunlet/DetourPath
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both detour different-distance numbers of a sunlet are two. -/

module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import OmegaBuild.Commands

/-! Native simple-path detours and detour different-distance sets of sunlets. -/

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

private theorem isGreatest_pathLength_leaf_core {n : ℕ} (i : Fin n) :
    IsGreatest {L : ℕ | ∃ p : (sunlet n).Walk (i, 1) (i, 0), p.IsPath ∧ p.length = L} 1 := by
  constructor
  · exact ⟨(core_to_leaf_adj i).symm.toWalk, (core_to_leaf_adj i).symm.isPath_toWalk, rfl⟩
  · rintro L ⟨p, hp, rfl⟩
    cases p with
    | @cons _ x _ h p =>
      have hx := neighbor_of_leaf h
      subst x
      have hnil := (Walk.isPath_iff_nil.mp hp.of_cons).eq_nil
      simp [hnil]

/-- At a single cycle index the detour is zero on the diagonal and one across the leaf edge. -/
theorem sunlet_isGreatest_pathLength_same_index {n : ℕ} (i : Fin n) (a b : Fin 2) :
    IsGreatest {L : ℕ | ∃ p : (sunlet n).Walk (i, a) (i, b), p.IsPath ∧ p.length = L}
      (if a = b then 0 else 1) := by
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    refine ⟨⟨nil, IsPath.nil, rfl⟩, ?_⟩
    rintro L ⟨p, hp, rfl⟩
    rw [(Walk.isPath_iff_nil.mp hp).eq_nil]
    exact Nat.le_refl 0
  · rw [ite_eq_right hab]
    rcases fin_two a with rfl | rfl <;> rcases fin_two b with rfl | rfl
    · exact (hab rfl).elim
    · obtain ⟨⟨p, hp, hlen⟩, hmax⟩ := isGreatest_pathLength_leaf_core i
      refine ⟨⟨p.reverse, hp.reverse, by simpa using hlen⟩, ?_⟩
      rintro L ⟨q, hq, hqLen⟩
      exact hmax ⟨q.reverse, hq.reverse, by simpa using hqLen⟩
    · exact isGreatest_pathLength_leaf_core i
    · exact (hab rfl).elim

/-- The detour distance in the sunlet is the greatest native simple-path length. -/
noncomputable def detourDistance {n : ℕ} (x y : Fin n × Fin 2) : ℕ :=
  sSup {L : ℕ | ∃ p : (sunlet n).Walk x y, p.IsPath ∧ p.length = L}

/-- A nonempty proper vertex set distinguished by each outside vertex in detour distance. -/
def IsDDD {n : ℕ} (S : Finset (Fin n × Fin 2)) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ ∧
    ∀ w ∉ S, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → detourDistance w u ≠ detourDistance w v

/-- Orders of the inclusion-maximal detour different-distance sets. -/
def maximalDDDOrders (n : ℕ) : Set ℕ :=
  {size | ∃ S : Finset (Fin n × Fin 2), Maximal IsDDD S ∧ S.card = size}

private def cycleDistance {n : ℕ} (i j : Fin n) : ℕ :=
  min (i - j).val (j - i).val

private theorem arc_pos {n : ℕ} [NeZero n] {i j : Fin n} (hij : i ≠ j) : 0 < (i - j).val :=
  Nat.pos_of_ne_zero fun h ↦ hij (sub_eq_zero.mp (Fin.ext h))

private theorem arc_add {n : ℕ} [NeZero n] {i j : Fin n} (hij : i ≠ j) :
    (j - i).val + (i - j).val = n := by
  have hpos := arc_pos hij.symm
  have hlt := (j - i).isLt
  have hnez : j - i ≠ 0 := sub_ne_zero.mpr hij.symm
  rw [← neg_sub j i, Fin.val_neg, ite_eq_right hnez]
  omega

private theorem arc_distances {n : ℕ} [NeZero n] (i j : Fin n) (m : ℕ)
    (hm : 0 < m) (hml : m < (j - i).val) :
    let k := i + (m : Fin n)
    k ≠ i ∧ k ≠ j ∧
      cycleDistance k i = min m (n - m) ∧
      cycleDistance k j = min ((j - i).val - m) (n - ((j - i).val - m)) := by
  dsimp
  let k := i + (m : Fin n)
  have hlt := (j - i).isLt
  have hki : (k - i).val = m := by
    simp [k, Fin.val_natCast, Nat.mod_eq_of_lt (show m < n by omega)]
  have hjk : (j - k).val = (j - i).val - m := by
    rw [show j - k = (j - i) - (m : Fin n) by simp [k, sub_add_eq_sub_sub]]
    rw [Fin.val_sub, Fin.val_natCast, Nat.mod_eq_of_lt (show m < n by omega)]
    rw [show n - m + (j - i).val = ((j - i).val - m) + n by omega]
    simp [Nat.mod_eq_of_lt (show (j - i).val - m < n by omega)]
  have hneI : k ≠ i := by
    intro h
    rw [h, sub_self] at hki
    have : (0 : Fin n).val = 0 := by simp
    omega
  have hneJ : k ≠ j := by
    intro h
    rw [h, sub_self] at hjk
    have : (0 : Fin n).val = 0 := by simp
    omega
  have hsumI := arc_add hneI.symm
  have hsumJ := arc_add hneJ
  refine ⟨hneI, hneJ, ?_, ?_⟩
  · unfold cycleDistance
    rw [hki, show (i - k).val = n - m by omega]
  · unfold cycleDistance
    rw [hjk, show (k - j).val = n - ((j - i).val - m) by omega, min_comm]

private theorem detour_of_index_ne {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (a b : Fin 2) :
    detourDistance (i, a) (j, b) = n - cycleDistance i j + a.val + b.val := by
  let : NeZero n := ⟨by omega⟩
  rw [detourDistance, (sunlet_isGreatest_pathLength_of_index_ne hn hij a b).csSup_eq]
  have hsum := arc_add hij
  unfold cycleDistance
  omega

private def FullIndex {n : ℕ} (S : Finset (Fin n × Fin 2)) (i : Fin n) : Prop :=
  (i, 0) ∈ S ∧ (i, 1) ∈ S

private theorem FullIndex.mem {n : ℕ} {S : Finset (Fin n × Fin 2)} {i : Fin n}
    (hi : FullIndex S i) (a : Fin 2) : (i, a) ∈ S := by
  obtain rfl | rfl := fin_two a
  · exact hi.1
  · exact hi.2

/-- A detour collision at a third index holds at both heights of that index. -/
private theorem full_of_collision {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n × Fin 2)}
    (hS : IsDDD S) {i j k : Fin n} {a b : Fin 2} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hi : (i, a) ∈ S) (hj : (j, b) ∈ S)
    (htie : cycleDistance k j + a.val = cycleDistance k i + b.val) :
    FullIndex S k := by
  have hle (l : Fin n) : cycleDistance k l ≤ n :=
    (min_le_left _ _).trans (Nat.le_of_lt (k - l).isLt)
  have hne : (i, a) ≠ (j, b) := fun h ↦ hij (congrArg Prod.fst h)
  have hm (c : Fin 2) : (k, c) ∈ S := by
    by_contra hw
    apply hS.2.2 (k, c) hw (i, a) hi (j, b) hj hne
    rw [detour_of_index_ne hn hki, detour_of_index_ne hn hkj]
    have := hle i
    have := hle j
    omega
  exact ⟨hm 0, hm 1⟩

private theorem full_of_close_distances {n : ℕ} (hn : 3 ≤ n)
    {S : Finset (Fin n × Fin 2)} (hS : IsDDD S) {i j k : Fin n}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : FullIndex S i) (hj : FullIndex S j)
    (h₁ : cycleDistance k j ≤ cycleDistance k i + 1)
    (h₂ : cycleDistance k i ≤ cycleDistance k j + 1) : FullIndex S k := by
  by_cases he : cycleDistance k i = cycleDistance k j
  · exact full_of_collision hn hS hij hki hkj hi.1 hj.1 (by omega)
  by_cases hl : cycleDistance k i < cycleDistance k j
  · exact full_of_collision hn hS hij hki hkj hi.1 hj.2 (by omega)
  · exact full_of_collision hn hS hij hki hkj hi.2 hj.1 (by omega)

private theorem midpoint_collision {n : ℕ} [NeZero n] {i j : Fin n} (a b : Fin 2)
    (hlen : 2 ≤ (j - i).val) (hparity : (j - i).val % 2 = (a.val + b.val) % 2) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧
      cycleDistance k j + a.val = cycleDistance k i + b.val := by
  let L := (j - i).val
  let m := if a.val ≤ b.val then L / 2 else (L + 1) / 2
  have hlt : L < n := (j - i).isLt
  have ha : a.val < 2 := a.isLt
  have hb : b.val < 2 := b.isLt
  obtain ⟨hpos, hm, hleft, hright, htie⟩ :
      0 < m ∧ m < L ∧ m ≤ n - m ∧ L - m ≤ n - (L - m) ∧
        L - m + a.val = m + b.val := by
    change 2 ≤ L at hlen
    change L % 2 = (a.val + b.val) % 2 at hparity
    dsimp [m]
    split <;> omega
  obtain ⟨hki, hkj, hdi, hdj⟩ := arc_distances i j m hpos hm
  rw [min_eq_left hleft] at hdi
  rw [min_eq_left hright] at hdj
  exact ⟨_, hki, hkj, by rw [hdi, hdj]; exact htie⟩

private def color {n : ℕ} (x : Fin n × Fin 2) : Fin 2 :=
  if n % 2 = 0 then ⟨(x.1.val + x.2.val) % 2, Nat.mod_lt _ (by decide)⟩ else x.2

private theorem full_of_same_color {n : ℕ} (hn : 4 ≤ n) {S : Finset (Fin n × Fin 2)}
    (hS : IsDDD S) {i j : Fin n} {a b : Fin 2} (hij : i ≠ j)
    (hi : (i, a) ∈ S) (hj : (j, b) ∈ S) (hc : color (i, a) = color (j, b)) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ FullIndex S k := by
  let : NeZero n := ⟨by omega⟩
  have hsum := arc_add hij
  have ha := a.isLt
  have hb := b.isLt
  have hparity (x y : Fin n) :
      n % 2 = 0 → ((y - x).val + x.val) % 2 = y.val % 2 := by
    intro heven
    have hadd : (y - x) + x = y := sub_add_cancel y x
    have he := congrArg Fin.val hadd
    rw [Fin.val_add_eq_ite] at he
    split at he <;> omega
  have hor : (2 ≤ (j - i).val ∧ (j - i).val % 2 = (a.val + b.val) % 2) ∨
      (2 ≤ (i - j).val ∧ (i - j).val % 2 = (b.val + a.val) % 2) := by
    by_cases heven : n % 2 = 0
    · have h := congrArg Fin.val hc
      simp only [color, ite_eq_left heven] at h
      have hjpar := hparity i j heven
      have hipar := hparity j i heven
      by_cases hlong : 2 ≤ (j - i).val
      · left
        omega
      · right
        omega
    · have he : a = b := by simpa only [color, ite_eq_right heven] using hc
      have hval := congrArg Fin.val he
      have hpos := arc_pos hij
      have hpos' := arc_pos hij.symm
      by_cases hEvenArc : (j - i).val % 2 = 0
      · left
        omega
      · right
        omega
  rcases hor with ⟨hlen, hp⟩ | ⟨hlen, hp⟩
  · obtain ⟨k, hki, hkj, htie⟩ := midpoint_collision a b hlen hp
    exact ⟨k, hki, hkj, full_of_collision (by omega) hS hij hki hkj hi hj htie⟩
  · obtain ⟨k, hkj, hki, htie⟩ := midpoint_collision b a hlen hp
    exact ⟨k, hki, hkj, full_of_collision (by omega) hS hij.symm hkj hki hj hi htie⟩

private theorem exists_height_of_color {n : ℕ} (i : Fin n) (c : Fin 2) :
    ∃ a : Fin 2, color (i, a) = c := by
  by_cases heven : n % 2 = 0
  · refine ⟨⟨(i.val + c.val) % 2, Nat.mod_lt _ (by decide)⟩, Fin.ext ?_⟩
    have hc := c.isLt
    simp only [color, ite_eq_left heven]
    omega
  · exact ⟨c, by simp [color, heven]⟩

private theorem full_of_adjacent {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n × Fin 2)}
    (hS : IsDDD S) {i j : Fin n} (hij : i ≠ j) (hstep : (j - i).val = 1)
    (hi : FullIndex S i) (hj : FullIndex S j) : ∀ k, FullIndex S k := by
  let : NeZero n := ⟨by omega⟩
  intro k
  by_cases hki : k = i
  · exact hki ▸ hi
  by_cases hkj : k = j
  · exact hkj ▸ hj
  let m := (k - j).val
  have hm : 0 < m := arc_pos hkj
  have hsum := arc_add hij
  have hlt : m < (i - j).val := by
    have hkn := (k - j).isLt
    have hne : (k - j).val ≠ (i - j).val := fun h ↦ hki (sub_left_inj.mp (Fin.ext h))
    change (k - j).val < (i - j).val
    omega
  have he : j + (m : Fin n) = k := by
    have hcast : (m : Fin n) = k - j := by
      apply Fin.ext
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (k - j).isLt]
    rw [hcast, add_comm, sub_add_cancel]
  obtain ⟨_, _, hdj, hdi⟩ := arc_distances j i m hm hlt
  rw [he] at hdi hdj
  apply full_of_close_distances hn hS hij hki hkj hi hj <;> rw [hdi, hdj] <;> omega

private theorem not_two_full_indices {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n × Fin 2)}
    (hS : IsDDD S) {i j : Fin n} (hij : i ≠ j)
    (hi : FullIndex S i) (hj : FullIndex S j) : False := by
  classical
  let : NeZero n := ⟨by omega⟩
  let P (r : ℕ) := ∃ u v : Fin n, u ≠ v ∧ FullIndex S u ∧ FullIndex S v ∧
    cycleDistance u v = r
  have hex : ∃ r, P r := ⟨_, i, j, hij, hi, hj, rfl⟩
  let r := Nat.find hex
  obtain ⟨u, v, huv, hu, hv, hdist⟩ := Nat.find_spec hex
  have hpos : 0 < r := by
    change cycleDistance u v = r at hdist
    unfold cycleDistance at hdist
    have h₁ := arc_pos huv
    have h₂ := arc_pos huv.symm
    omega
  have hnear (x y : Fin n) (hxy : x ≠ y) (hx : FullIndex S x) (hy : FullIndex S y)
      (hlen : (y - x).val = r) : False := by
    by_cases hunit : r = 1
    · have hall := full_of_adjacent hn hS hxy (hlen.trans hunit) hx hy
      apply hS.2.1
      ext z
      exact ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ (hall z.1).mem z.2⟩
    · let m := r / 2
      have hm : 0 < m := by dsimp [m]; omega
      have hml : m < (y - x).val := by dsimp [m]; omega
      have hrn : r < n := hlen ▸ (y - x).isLt
      obtain ⟨hkx, hky, hdx, hdy⟩ := arc_distances x y m hm hml
      rw [min_eq_left (by dsimp [m]; omega)] at hdx
      rw [hlen, min_eq_left (by dsimp [m]; omega)] at hdy
      have hk := full_of_close_distances hn hS hxy hkx hky hx hy
        (by rw [hdx, hdy]; dsimp [m]; omega) (by rw [hdx, hdy]; dsimp [m]; omega)
      have hsmaller : P m := ⟨_, x, hkx, hk, hx, hdx⟩
      have hmin : r ≤ m := Nat.find_min' hex hsmaller
      omega
  change min (u - v).val (v - u).val = r at hdist
  by_cases hle : (u - v).val ≤ (v - u).val
  · exact hnear v u huv.symm hv hu ((min_eq_left hle).symm.trans hdist)
  · exact hnear u v huv hu hv ((min_eq_right (by omega)).symm.trans hdist)

private def verticalPair {n : ℕ} (i : Fin n) : Finset (Fin n × Fin 2) :=
  {(i, 0), (i, 1)}

private theorem mem_verticalPair {n : ℕ} {i : Fin n} {x : Fin n × Fin 2} :
    x ∈ verticalPair i ↔ x.1 = i := by
  obtain ⟨j, a⟩ := x
  obtain rfl | rfl := fin_two a <;> simp [verticalPair, Prod.mk.injEq]

private theorem card_verticalPair {n : ℕ} (i : Fin n) : (verticalPair i).card = 2 := by
  have h : (i, (0 : Fin 2)) ≠ (i, (1 : Fin 2)) := by simp
  simp [verticalPair, h]

private theorem verticalPair_isDDD {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    IsDDD (verticalPair i) := by
  refine ⟨⟨(i, 0), mem_verticalPair.mpr rfl⟩, ?_, ?_⟩
  · intro h
    have hncard : (verticalPair i).card = n * 2 := by rw [h]; simp [Fintype.card_prod]
    rw [card_verticalPair] at hncard
    omega
  · rintro ⟨k, c⟩ hw ⟨j, a⟩ hu ⟨l, b⟩ hv huv
    have hki : k ≠ i := fun h ↦ hw (mem_verticalPair.mpr h)
    have hj : j = i := mem_verticalPair.mp hu
    have hl : l = i := mem_verticalPair.mp hv
    subst j
    subst l
    rw [detour_of_index_ne hn hki, detour_of_index_ne hn hki]
    intro h
    have hab : a.val = b.val := by omega
    exact huv (Prod.ext rfl (Fin.ext hab))

private theorem card_le_two_of_isDDD {n : ℕ} (hn : 4 ≤ n)
    {S : Finset (Fin n × Fin 2)} (hS : IsDDD S) : S.card ≤ 2 := by
  by_cases hfull : ∃ i, FullIndex S i
  · obtain ⟨i, hi⟩ := hfull
    refine (Finset.card_le_card ?_).trans (card_verticalPair i).le
    rintro ⟨j, b⟩ hj
    apply mem_verticalPair.mpr
    by_contra hji
    change j ≠ i at hji
    obtain ⟨a, hc⟩ := exists_height_of_color i (color (j, b))
    obtain ⟨k, hki, _, hk⟩ := full_of_same_color hn hS hji.symm (hi.mem a) hj hc
    exact not_two_full_indices (by omega) hS hki hk hi
  · have hinj : Set.InjOn color (↑S : Set (Fin n × Fin 2)) := by
      rintro ⟨i, a⟩ hi ⟨j, b⟩ hj hc
      by_cases hij : i = j
      · subst j
        have hab : a = b := by
          by_contra hab
          apply hfull
          refine ⟨i, ?_⟩
          obtain rfl | rfl := fin_two a <;> obtain rfl | rfl := fin_two b
          · exact (hab rfl).elim
          · exact ⟨hi, hj⟩
          · exact ⟨hj, hi⟩
          · exact (hab rfl).elim
        exact Prod.ext rfl hab
      · obtain ⟨k, _, _, hk⟩ := full_of_same_color hn hS hij hi hj hc
        exact (hfull ⟨k, hk⟩).elim
    simpa using Finset.card_le_card_of_injOn color (t := Finset.univ) (by simp) hinj

/-- Both extrema in Definition 1.1 for the sunlet clause of Problem 4.3.
The authors' Theorem 2.14(i) already gives the triangle sunlet. -/
theorem sunlet_detour_numbers {n : ℕ} (hn : 4 ≤ n) :
    sInf (maximalDDDOrders n) = 2 ∧ sSup (maximalDDDOrders n) = 2 := by
  have hmaxPair (i : Fin n) : Maximal IsDDD (verticalPair i) := by
    refine ⟨verticalPair_isDDD (by omega) i, ?_⟩
    intro T hT hsub
    have hcard := card_le_two_of_isDDD hn hT
    have hEq := Finset.eq_of_subset_of_card_le hsub (by rwa [card_verticalPair])
    exact hEq.ge
  have htwo : 2 ∈ maximalDDDOrders n := by
    let i : Fin n := ⟨0, by omega⟩
    exact ⟨verticalPair i, hmaxPair i, card_verticalPair i⟩
  have hall : ∀ size ∈ maximalDDDOrders n, size = 2 := by
    rintro size ⟨S, hS, rfl⟩
    have hle := card_le_two_of_isDDD hn hS.1
    obtain ⟨x, hx⟩ := hS.1.1
    by_contra hne
    have hsmall : S.card ≤ 1 := by omega
    have hsub : S ⊆ verticalPair x.1 := by
      intro y hy
      have he := Finset.card_le_one.mp hsmall y hy x hx
      exact mem_verticalPair.mpr (congrArg Prod.fst he)
    have hrev := hS.2 (verticalPair_isDDD (by omega) x.1) hsub
    have hcard := Finset.card_le_card hrev
    rw [card_verticalPair] at hcard
    omega
  exact ⟨(show IsLeast (maximalDDDOrders n) 2 from
    ⟨htwo, fun x hx ↦ (hall x hx).ge⟩).csInf_eq,
    (show IsGreatest (maximalDDDOrders n) 2 from
    ⟨htwo, fun x hx ↦ (hall x hx).le⟩).csSup_eq⟩

end AlsinaiAhmed.Sunlet
