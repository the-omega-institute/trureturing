/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete native-circle complements supply actual a/b cut pieces. -/
import D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open Equiv
open Fin.NatCast

/-- A full native circle is independently specified by the actual tuple,
modulo rotations and whole reversal. -/
def Circle {m : ℕ} (z v : Configuration m) : Prop :=
  configurationCycle v = configurationCycle z ∨
    configurationCycle v = (configurationCycle z).reverse

/-- The native dihedral position and reflection coordinates within one circle. -/
def circleCoordinate {m : ℕ} (z : Configuration m)
    (p : Fin (m + 1) × Bool) : Configuration m :=
  z * finCycle p.1 * (if p.2 then a m else 1)

private theorem circleCoordinate_injective {m : ℕ} (hm : 3 ≤ m)
    (z : Configuration m) : Function.Injective (circleCoordinate z) := by
  intro p q he
  let gap0 : Fin m := ⟨0, by omega⟩
  have hsub : coordinateEquiv hm z (gap0, p) = coordinateEquiv hm z (gap0, q) := by
    apply Subtype.ext
    simpa only [coordinateEquiv, Equiv.ofBijective_apply, coordinate, gapAnchor,
      gap0, pow_zero, mul_one, circleCoordinate] using he
  have hi := (coordinateEquiv hm z).injective hsub
  exact congrArg Prod.snd hi

theorem native_configurationCycle_rotation {m : ℕ} (z : Configuration m)
    (r : Fin (m + 1)) : configurationCycle (z * finCycle r) = configurationCycle z := by
  have hr : finRotate (m + 1) ^ r.val = finCycle r := by
    simpa using rotate_pow_eq_cycle (m := m) r.val
  rw [← hr]
  apply Cycle.coe_eq_coe.mpr
  rw [rotate_pow_list]
  exact List.IsRotated.symm ⟨r.val, rfl⟩

theorem native_configurationCycle_reversal {m : ℕ} (z : Configuration m) :
    configurationCycle (z * a m) = (configurationCycle z).reverse := by
  change ((List.ofFn (z * a m) : List (Fin (m + 1))) : Cycle (Fin (m + 1))) = _
  rw [full_reverse_list]
  rfl

private theorem circleCoordinate_mem {m : ℕ} (z : Configuration m)
    (p : Fin (m + 1) × Bool) : Circle z (circleCoordinate z p) := by
  rcases p with ⟨r, s⟩
  cases s
  · left
    simpa only [circleCoordinate, Bool.false_eq_true, ↓reduceIte, mul_one] using
      native_configurationCycle_rotation z r
  · right
    simpa only [circleCoordinate, ↓reduceIte, native_configurationCycle_reversal,
      native_configurationCycle_rotation]

private theorem positive_coordinate {m : ℕ} (z v : Configuration m)
    (hv : configurationCycle v = configurationCycle z) :
    ∃ r : Fin (m + 1), z * finCycle r = v := by
  obtain ⟨k, hk⟩ := (Cycle.coe_eq_coe.mp hv).symm
  have he : z * finRotate (m + 1) ^ k = v := by
    apply Equiv.ext
    exact congrFun (List.ofFn_injective ((rotate_pow_list z k).trans hk))
  refine ⟨(k : Fin (m + 1)), ?_⟩
  rwa [rotate_pow_eq_cycle] at he

private theorem circleCoordinate_surjective {m : ℕ} (z v : Configuration m)
    (hv : Circle z v) : ∃ p : Fin (m + 1) × Bool, circleCoordinate z p = v := by
  rcases hv with hv | hv
  · obtain ⟨r, hr⟩ := positive_coordinate z v hv
    exact ⟨(r, false), by simpa [circleCoordinate] using hr⟩
  · have hva : configurationCycle (v * a m) = configurationCycle z := by
      rw [native_configurationCycle_reversal, hv, Cycle.reverse_reverse]
    obtain ⟨r, hr⟩ := positive_coordinate z (v * a m) hva
    refine ⟨(r, true), ?_⟩
    simp only [circleCoordinate, ↓reduceIte, hr, mul_assoc, a_sq, mul_one]

/-- The actual dihedral coordinates exhaust the independently defined circle. -/
noncomputable def circleEquiv {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    (Fin (m + 1) × Bool) ≃ {v : Configuration m // Circle z v} :=
  Equiv.ofBijective
    (fun p => ⟨circleCoordinate z p, circleCoordinate_mem z p⟩)
    ⟨fun p q he => circleCoordinate_injective hm z (congrArg Subtype.val he),
      fun v => by
        obtain ⟨p, hp⟩ := circleCoordinate_surjective z v.val v.property
        exact ⟨p, Subtype.ext hp⟩⟩

private theorem h_trace {m : ℕ} (z : Configuration m) (k : ℕ) :
    List.scanl (· * ·) z (uWord m k) =
      (List.ofFn (fun j : Fin (k + 1) =>
        [z * finRotate (m + 1) ^ j.val,
          z * finRotate (m + 1) ^ j.val * a m])).flatten := by
  induction k generalizing z with
  | zero => simp [uWord, List.ofFn_succ]
  | succ k ih =>
    rw [uWord, List.scanl_cons, List.scanl_cons, ih, List.ofFn_succ]
    simp [pow_succ', mul_assoc, ab_eq_rotate]

private def circlePairs (m : ℕ) : List (Fin (m + 1) × Bool) :=
  (List.ofFn (fun j : Fin (m + 1) => [(j, false), (j, true)])).flatten

private theorem circlePairs_nodup (m : ℕ) : (circlePairs m).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    simp
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    rw [List.disjoint_left]
    intro x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals
      have he := congrArg (fun p : Fin (m + 1) × Bool => p.1.val) (hx.symm.trans hy)
      simp only at he
      have hij' : i.val < j.val := hij
      omega

private theorem circlePairs_mem {m : ℕ} (p : Fin (m + 1) × Bool) :
    p ∈ circlePairs m := by
  apply List.mem_flatten.mpr
  refine ⟨[(p.1, false), (p.1, true)], List.mem_ofFn.mpr ⟨p.1, rfl⟩, ?_⟩
  cases p with
  | mk j s => cases s <;> simp

private theorem h_trace_coordinates {m : ℕ} (z : Configuration m) :
    List.scanl (· * ·) z (uWord m m) = (circlePairs m).map (circleCoordinate z) := by
  rw [h_trace]
  simp [circlePairs, List.map_flatten, Function.comp_def, circleCoordinate,
    cycle_zero, rotate_pow_eq_cycle]

private theorem h_trace_nodup {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    (List.scanl (· * ·) z (uWord m m)).Nodup := by
  rw [h_trace_coordinates]
  exact (circlePairs_nodup m).map (circleCoordinate_injective hm z)

private theorem h_trace_mem {m : ℕ} (z v : Configuration m) :
    v ∈ List.scanl (· * ·) z (uWord m m) ↔ Circle z v := by
  rw [h_trace_coordinates, List.mem_map]
  constructor
  · rintro ⟨p, _, rfl⟩
    exact circleCoordinate_mem z p
  · intro hv
    obtain ⟨p, hp⟩ := circleCoordinate_surjective z v hv
    exact ⟨p, circlePairs_mem p, hp⟩

private theorem word_foldl {m : ℕ} (z : Configuration m)
    (l : List (Configuration m)) : l.foldl (· * ·) z = z * l.prod := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

private theorem word_chain {m : ℕ} (G : SimpleGraph (Configuration m))
    (l : List (Configuration m)) (hstep : ∀ z g, g ∈ l → G.Adj z (z * g))
    (z : Configuration m) : (List.scanl (· * ·) z l).IsChain G.Adj := by
  induction l generalizing z with
  | nil => simp
  | cons g gs ih =>
    rw [List.scanl_cons, List.isChain_cons]
    constructor
    · intro y hy
      simp only [List.head?_scanl, Option.mem_some_iff] at hy
      subst y
      exact hstep z g (by simp)
    · exact ih (fun z x hx => hstep z x (List.mem_cons_of_mem _ hx)) (z * g)

private theorem h_mem {m k : ℕ} {g : Configuration m} (hg : g ∈ uWord m k) :
    g = a m ∨ g = b m := by
  induction k with
  | zero => exact Or.inl (by simpa [uWord] using hg)
  | succ k ih =>
    simp only [uWord, List.mem_cons] at hg
    rcases hg with hg | hg | hg
    · exact Or.inl hg
    · exact Or.inr hg
    · exact ih hg

private theorem a_ne_one {m : ℕ} (hm : 3 ≤ m) : a m ≠ 1 := by
  intro he
  have hv := congrArg (fun g : Configuration m => (g 0).val) he
  simp [a_apply] at hv
  omega

private theorem b_ne_one {m : ℕ} (hm : 3 ≤ m) : b m ≠ 1 := by
  intro he
  have hv := congrArg (fun g : Configuration m => (g 0).val) he
  simp [b_apply, show 0 < m by omega] at hv
  omega

private theorem h_product (m : ℕ) : (uWord m m).prod = b m := by
  rw [uWord_product, rotate_pow_eq_cycle, b_eq_cycle_a]
  congr 1
  have hr : (m : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp
  rw [hr, ← Fin.neg_last m, neg_neg]

/-- Deleting a native b-edge leaves its complete actual circle complement.
The support is the literal H word and membership is the independent bracelet
domain, not the set of vertices found by a search. -/
theorem native_b_complement {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    ∃ w : ((SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).deleteEdges
        {s(z, z * b m)}).Walk z (z * b m),
      w.IsPath ∧ w.length = 2 * (m + 1) - 1 ∧
        w.support = List.scanl (· * ·) z (uWord m m) ∧
        (∀ v : Configuration m, v ∈ w.support ↔ Circle z v) := by
  let G := SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))
  let xs := List.scanl (· * ·) z (uWord m m)
  have hne : xs ≠ [] := List.scanl_ne_nil
  have hc : xs.IsChain G.Adj := by
    apply word_chain
    intro v g hg
    rw [SimpleGraph.mulCayley_adj']
    have hg' := h_mem hg
    have hg1 : g ≠ 1 := hg'.elim (fun he => he ▸ a_ne_one hm)
      (fun he => he ▸ b_ne_one hm)
    constructor
    · intro he
      apply hg1
      exact mul_left_cancel (by simpa only [mul_one] using he.symm)
    · refine ⟨g, ?_, Or.inl rfl⟩
      simpa using hg'
  let raw := SimpleGraph.Walk.ofSupport xs hne hc
  let w := raw.copy (List.head_scanl hne)
    (by rw [List.getLast_scanl, word_foldl, h_product])
  have hs : w.support = xs := by
    simp [w, raw]
  have hp : w.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hs]
    exact h_trace_nodup hm z)
  have hlen : w.length = 2 * (m + 1) - 1 := by
    have hh := congrArg List.length hs
    simp only [SimpleGraph.Walk.length_support, xs, List.length_scanl, uWord_length] at hh
    omega
  have hmissing : s(z, z * b m) ∉ w.edges := by
    intro he
    have hl := hp.length_eq_one_of_mem_edges he
    rw [hlen] at hl
    omega
  refine ⟨w.toDeleteEdge _ hmissing, ?_, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    change (w.transfer _ _).support.Nodup
    rw [SimpleGraph.Walk.support_transfer]
    exact hp.support_nodup
  · change (w.transfer _ _).length = _
    rw [SimpleGraph.Walk.length_transfer]
    exact hlen
  · change (w.transfer _ _).support = _
    rw [SimpleGraph.Walk.support_transfer]
    exact hs
  · intro v
    change v ∈ (w.transfer _ _).support ↔ _
    rw [SimpleGraph.Walk.support_transfer, hs]
    exact h_trace_mem z v

/-- The complementary a-cut piece uses the same complete independent domain.
It starts with the retained b-edge and reverses the tail of the full H piece. -/
theorem native_a_complement {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    ∃ w : ((SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).deleteEdges
        {s(z, z * a m)}).Walk z (z * a m),
      w.IsPath ∧ w.length = 2 * (m + 1) - 1 ∧
        w.support = z :: (List.scanl (· * ·) z (uWord m m)).tail.reverse ∧
        (∀ v : Configuration m, v ∈ w.support ↔ Circle z v) := by
  let G := SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))
  obtain ⟨w0, _, _, hw0, _⟩ := native_b_complement hm z
  let q : G.Walk z (z * b m) := w0.mapLe (SimpleGraph.deleteEdges_le _)
  have hqs : q.support = List.scanl (· * ·) z (uWord m m) := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    exact hw0
  have hqn : ¬q.Nil := by
    intro he
    have hs := congrArg List.length hqs
    simp only [SimpleGraph.Walk.length_support, List.length_scanl, uWord_length] at hs
    have hz := he.length_eq_zero
    omega
  have hqa : q.snd = z * a m := by
    rw [SimpleGraph.Walk.snd_eq_support_getElem_one hqn]
    cases m with
    | zero => omega
    | succ m => simp [hqs, uWord, List.scanl_cons]
  have hb : G.Adj z (z * b m) := by
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨?_, b m, by simp, Or.inl rfl⟩
    intro he
    exact b_ne_one hm (mul_left_cancel (by simpa only [mul_one] using he.symm))
  let raw := q.tail.reverse.cons hb
  let w := raw.copy rfl hqa
  have hs : w.support = z :: (List.scanl (· * ·) z (uWord m m)).tail.reverse := by
    simp only [w, raw, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_tail_of_not_nil q hqn,
      hqs]
  have hperm : w.support.Perm (List.scanl (· * ·) z (uWord m m)) := by
    rw [hs]
    have he : z :: (List.scanl (· * ·) z (uWord m m)).tail =
        List.scanl (· * ·) z (uWord m m) := by
      cases m with
      | zero => simp [uWord]
      | succ m => simp [uWord, List.scanl_cons]
    rw [← he]
    exact (List.reverse_perm _).cons z
  have hp : w.IsPath := SimpleGraph.Walk.IsPath.mk'
    (hperm.nodup_iff.mpr (h_trace_nodup hm z))
  have hlen : w.length = 2 * (m + 1) - 1 := by
    have hh := hperm.length_eq
    rw [SimpleGraph.Walk.length_support, List.length_scanl, uWord_length] at hh
    omega
  have hmissing : s(z, z * a m) ∉ w.edges := by
    intro he
    have hl := hp.length_eq_one_of_mem_edges he
    rw [hlen] at hl
    omega
  refine ⟨w.toDeleteEdge _ hmissing, ?_, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    change (w.transfer _ _).support.Nodup
    rw [SimpleGraph.Walk.support_transfer]
    exact hp.support_nodup
  · change (w.transfer _ _).length = _
    rw [SimpleGraph.Walk.length_transfer]
    exact hlen
  · change (w.transfer _ _).support = _
    rw [SimpleGraph.Walk.support_transfer]
    exact hs
  · intro v
    change v ∈ (w.transfer _ _).support ↔ _
    rw [SimpleGraph.Walk.support_transfer, hperm.mem_iff]
    exact h_trace_mem z v

#print axioms circleEquiv
#print axioms native_b_complement
#print axioms native_a_complement

private theorem native_a_ne_b {m : ℕ} (hm : 3 ≤ m) : a m ≠ b m := by
  intro h
  have he := congrArg (fun z : Configuration m => (z (Fin.last m)).val) h
  simp only [a_apply, Fin.val_rev, Fin.val_last, b_apply,
    Nat.sub_self, lt_self_iff_false, if_false] at he
  omega

private theorem native_b_sq (m : ℕ) : b m * b m = 1 := by
  apply Equiv.ext
  intro i
  exact PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
    (L := m) (by omega) i

private theorem native_adj_neighbors {m : ℕ} (x y : Configuration m)
    (h : (SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).Adj x y) :
    y = x * a m ∨ y = x * b m := by
  rw [SimpleGraph.mulCayley_adj'] at h
  obtain ⟨_, g, hg, he⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · left
    rcases he with he | he
    · exact he.symm
    · have hh := congrArg (· * a m) he
      simpa only [mul_assoc, a_sq, mul_one] using hh.symm
  · right
    rcases he with he | he
    · exact he.symm
    · have hh := congrArg (· * b m) he
      simpa only [mul_assoc, native_b_sq, mul_one] using hh.symm

private theorem native_cycle_retains_edges {m : ℕ} (hm : 3 ≤ m)
    {z : Configuration m}
    (w : (SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).Walk z z)
    (hw : w.IsCycle) (x : Configuration m) (hx : x ∈ w.support) :
    s(x, x * a m) ∈ w.edges ∧ s(x, x * b m) ∈ w.edges := by
  have hsubset : w.toSubgraph.neighborSet x ⊆ {x * a m, x * b m} := by
    intro y hy
    exact (native_adj_neighbors x y hy.adj_sub).elim Or.inl Or.inr
  have hne : x * a m ≠ x * b m := fun h => native_a_ne_b hm (mul_left_cancel h)
  have he := Set.eq_of_subset_of_ncard_le hsubset (by
    rw [Set.ncard_pair hne, hw.ncard_neighborSet_toSubgraph_eq_two hx])
  constructor
  · apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
    change x * a m ∈ w.toSubgraph.neighborSet x
    rw [he]
    exact Or.inl rfl
  · apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
    change x * b m ∈ w.toSubgraph.neighborSet x
    rw [he]
    exact Or.inr rfl

/-- Every genuine full native circle complement contains exactly all other
native a/b edges. In particular, the b edge at a later insertion contact is
retained whenever it differs from this complement's actual deleted edge. -/
theorem native_complement_edge_inventory {m : ℕ} (hm : 3 ≤ m)
    (z g : Configuration m) (hg : g = a m ∨ g = b m)
    (w : (SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).Walk z (z * g))
    (hp : w.IsPath) (hl : w.length = 2 * (m + 1) - 1)
    (hs : ∀ x, x ∈ w.support ↔ Circle z x)
    (x h : Configuration m) (hx : Circle z x) (hh : h = a m ∨ h = b m) :
    s(x, x * h) ∈ w.edges ↔ s(x, x * h) ≠ s(z, z * g) := by
  have hg1 : g ≠ 1 := hg.elim (fun h => h ▸ a_ne_one hm)
    (fun h => h ▸ b_ne_one hm)
  have hadj : (SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).Adj z (z * g) := by
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨?_, g, by simpa using hg, Or.inl rfl⟩
    intro he
    exact hg1 (mul_left_cancel (by simpa only [mul_one] using he.symm))
  have hmissing : s(z, z * g) ∉ w.edges := by
    intro he
    have heq := hp.length_eq_one_of_mem_edges he
    omega
  let q := w.reverse.cons hadj
  have hq : q.IsCycle := by
    apply (SimpleGraph.Walk.cons_isCycle_iff w.reverse hadj).mpr
    refine ⟨hp.reverse, ?_⟩
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hmissing
  have hxq : x ∈ q.support := by
    simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse,
      List.mem_cons, List.mem_reverse]
    exact Or.inr ((hs x).mpr hx)
  have hedge : s(x, x * h) ∈ q.edges := by
    rcases hh with rfl | rfl
    · exact (native_cycle_retains_edges hm q hq x hxq).1
    · exact (native_cycle_retains_edges hm q hq x hxq).2
  simp only [q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_reverse,
    List.mem_cons, List.mem_reverse] at hedge
  constructor
  · intro he hsame
    exact hmissing (hsame ▸ he)
  · intro hne
    exact hedge.resolve_left hne

/-- Actual native a/b edges belonging to an independently specified circle. -/
def NativeCircleEdge {m : ℕ} (z : Configuration m) (e : Sym2 (Configuration m)) : Prop :=
  ∃ x h : Configuration m, Circle z x ∧ (h = a m ∨ h = b m) ∧ e = s(x, x * h)

/-- An arbitrary undirected edge belongs to an actual complete native
complement exactly when it is a native circle edge outside its literal cut. -/
theorem native_complement_full_edge_inventory {m : ℕ} (hm : 3 ≤ m)
    (z g : Configuration m) (hg : g = a m ∨ g = b m)
    (w : (SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m))).Walk z (z * g))
    (hp : w.IsPath) (hl : w.length = 2 * (m + 1) - 1)
    (hs : ∀ x, x ∈ w.support ↔ Circle z x) (e : Sym2 (Configuration m)) :
    e ∈ w.edges ↔ NativeCircleEdge z e ∧ e ≠ s(z, z * g) := by
  constructor
  · intro he
    obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
    have hx := (hs x).mp (w.fst_mem_support_of_mem_edges he)
    rcases native_adj_neighbors x y (w.adj_of_mem_edges he) with hy | hy
    · subst y
      exact ⟨⟨x, a m, hx, Or.inl rfl, rfl⟩,
        (native_complement_edge_inventory hm z g hg w hp hl hs x (a m) hx
          (Or.inl rfl)).mp he⟩
    · subst y
      exact ⟨⟨x, b m, hx, Or.inr rfl, rfl⟩,
        (native_complement_edge_inventory hm z g hg w hp hl hs x (b m) hx
          (Or.inr rfl)).mp he⟩
  · rintro ⟨⟨x, h, hx, hh, rfl⟩, hne⟩
    exact (native_complement_edge_inventory hm z g hg w hp hl hs x h hx hh).mpr hne

#print axioms native_complement_edge_inventory
private theorem circle_b_reversal {m : ℕ} (v : Configuration m) :
    configurationCycle (v * b m) = (configurationCycle v).reverse := by
  have hr : configurationCycle (v * a m * (a m * b m)) =
      configurationCycle (v * a m) := by
    rw [ab_eq_rotate]
    apply Cycle.coe_eq_coe.mpr
    rw [show List.ofFn (v * a m * finRotate (m + 1)) =
      (List.ofFn (v * a m)).rotate 1 from by
        simpa only [pow_one] using rotate_pow_list (v * a m) 1]
    exact List.IsRotated.symm ⟨1, rfl⟩
  have he : v * a m * (a m * b m) = v * b m := by
    rw [mul_assoc, ← mul_assoc (a m), a_sq, one_mul]
  rw [he, native_configurationCycle_reversal] at hr
  exact hr

private theorem circle_native_closed {m : ℕ} (z x g : Configuration m)
    (hx : Circle z x) (hg : g = a m ∨ g = b m) : Circle z (x * g) := by
  have hr : configurationCycle (x * g) = (configurationCycle x).reverse := by
    rcases hg with rfl | rfl
    · exact native_configurationCycle_reversal x
    · exact circle_b_reversal x
  rcases hx with hx | hx
  · exact Or.inr (hr.trans (congrArg Cycle.reverse hx))
  · exact Or.inl (by rw [hr, hx, Cycle.reverse_reverse])

/-- Every endpoint of an actual native circle edge lies in its independently
specified complete rotation/reversal circle. -/
theorem native_circle_edge_endpoint {m : ℕ} (z v : Configuration m)
    (e : Sym2 (Configuration m)) (he : NativeCircleEdge z e) (hv : v ∈ e) :
    Circle z v := by
  obtain ⟨x, g, hx, hg, rfl⟩ := he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact hx
  · exact circle_native_closed z x g hx hg


#print axioms native_complement_full_edge_inventory
#print axioms native_circle_edge_endpoint

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
