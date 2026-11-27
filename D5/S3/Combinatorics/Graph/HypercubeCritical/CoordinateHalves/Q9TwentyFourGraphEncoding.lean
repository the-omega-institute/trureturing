/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourGraphEncoding
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-four-half-embedding-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Cover connected triangle-free cubic graphs on twelve vertices with the finite search. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourDiscovery
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
import Batteries.Tactic.OpenPrivate

/-! Relate graph operations to the row masks used by the finite graph search. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding

open private Graph adjacent join degree canJoin decode labels representatives relabels
  candidate_has_witness from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch

open private Choices extendWith FollowsDiscovery candidates mem_search from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch

open private seenAfter seenAfter_nodup seen_prefix discoveryLabels still_available
  new_neighbors_contiguous from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourDiscovery

private def encode (edge : Fin 12 → Fin 12 → Bool) : Graph :=
  Array.ofFn fun i => (BitVec.ofBoolListLE (List.ofFn (edge i))).toNat

private theorem encoded_row (edge : Fin 12 → Fin 12 → Bool) (i : Fin 12) :
    (encode edge)[i.val]! = (BitVec.ofBoolListLE (List.ofFn (edge i))).toNat := by
  unfold encode
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]

private theorem encoded_adj (edge : Fin 12 → Fin 12 → Bool) (i j : Fin 12) :
    adjacent (encode edge) i.val j.val = edge i j := by
  rw [adjacent, encoded_row]
  change (BitVec.ofBoolListLE (List.ofFn (edge i))).getLsbD j.val = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt)]
  simp only [Option.getD_some, List.getElem_ofFn]

private theorem encoded_outside (edge : Fin 12 → Fin 12 → Bool) (i : Fin 12)
    {j : Nat} (hj : 12 ≤ j) : adjacent (encode edge) i.val j = false := by
  rw [adjacent, encoded_row]
  change (BitVec.ofBoolListLE (List.ofFn (edge i))).getLsbD j = _
  simp [List.getD_eq_getElem?_getD, Nat.not_lt.mpr hj]

private theorem size_encode (edge : Fin 12 → Fin 12 → Bool) : (encode edge).size = 12 := by
  simp [encode]

private theorem graph_ext {g h : Graph} (hsize : g.size = h.size)
    (hbits : ∀ i < g.size, ∀ j, adjacent g i j = adjacent h i j) : g = h := by
  apply Array.ext hsize
  intro i hi hi'
  have hr : g[i]! = h[i]! := Nat.eq_of_testBit_eq (hbits i hi)
  simpa only [getElem!_pos g i hi, getElem!_pos h i hi'] using hr

private theorem adjacent_join (g : Graph) (u v : Nat)
    (hu : u < g.size) (hv : v < g.size) (hne : u ≠ v) (i j : Nat) :
    adjacent (join g u v) i j =
      (adjacent g i j || (i == u && j == v) || (i == v && j == u)) := by
  have hv' : v < (g.set! u (g[u]! ||| (1 <<< v))).size := by
    rwa [Array.size_set!]
  by_cases hiu : i = u
  · subst i
    simp only [adjacent, join, Array.getElem!_set!_ne _ v u _ hne.symm,
      Array.getElem!_set!_self _ _ _ hu, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.testBit_two_pow, beq_self_eq_true, Bool.true_and]
    have huv : (u == v) = false := beq_eq_false_iff_ne.mpr hne
    simp only [huv, Bool.false_and, Bool.or_false]
    by_cases hj : v = j
    · subst j
      simp
    · have h : (j == v) = false := beq_eq_false_iff_ne.mpr (Ne.symm hj)
      simp [hj, h]
  · by_cases hiv : i = v
    · subst i
      have hs : (join g u v)[v]! = (g[v]! ||| (1 <<< u)) := by
        unfold join
        exact Array.getElem!_set!_self _ _ _ hv'
      simp only [adjacent, hs, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.testBit_two_pow, beq_self_eq_true, Bool.true_and]
      have hvu : (v == u) = false := beq_eq_false_iff_ne.mpr hne.symm
      simp only [hvu, Bool.false_and, Bool.or_false]
      by_cases hj : u = j
      · subst j
        simp
      · have h : (j == u) = false := beq_eq_false_iff_ne.mpr (Ne.symm hj)
        simp [hj, h]
    · have hu' : (i == u) = false := by simp [hiu]
      have hv' : (i == v) = false := by simp [hiv]
      simp only [adjacent, join, Array.getElem!_set!_ne _ u i _ (Ne.symm hiu),
        Array.getElem!_set!_ne _ v i _ (Ne.symm hiv), hu', hv', Bool.false_and, Bool.or_false]

/-- Adding an edge updates its two symmetric entries in the mask matrix. -/
private theorem join_encoded (edge : Fin 12 → Fin 12 → Bool) (u v : Fin 12)
    (hne : u ≠ v) :
    join (encode edge) u.val v.val =
      encode (fun i j => edge i j || (i == u && j == v) || (i == v && j == u)) := by
  let f : Fin 12 → Fin 12 → Bool :=
    fun i j => edge i j || (i == u && j == v) || (i == v && j == u)
  have hu : u.val < (encode edge).size := (size_encode edge).symm ▸ u.isLt
  have hv : v.val < (encode edge).size := (size_encode edge).symm ▸ v.isLt
  have hneq : u.val ≠ v.val := fun he => hne (Fin.ext he)
  change join (encode edge) u.val v.val = encode f
  have hsize : (join (encode edge) u.val v.val).size = 12 := by
    simp only [join, Array.size_set!, size_encode]
  apply graph_ext (hsize.trans (size_encode f).symm)
  intro i hi j
  let a : Fin 12 := ⟨i, hsize ▸ hi⟩
  rw [adjacent_join _ _ _ hu hv hneq]
  by_cases hjlt : j < 12
  · let b : Fin 12 := ⟨j, hjlt⟩
    have he := encoded_adj edge a b
    have hf := encoded_adj f a b
    change adjacent (encode edge) i j = edge a b at he
    change adjacent (encode f) i j = f a b at hf
    rw [he, hf]
    rfl
  · have ho : 12 ≤ j := Nat.le_of_not_gt hjlt
    have hjU : j ≠ u.val := by omega
    have hjV : j ≠ v.val := by omega
    have he := encoded_outside edge a ho
    have hf := encoded_outside f a ho
    change adjacent (encode edge) i j = false at he
    change adjacent (encode f) i j = false at hf
    simp [he, hf, hjU, hjV]

private theorem degree_eq_card (g : Graph) (i : Nat) :
    degree g i = ((Finset.range 12).filter fun j => adjacent g i j = true).card := by
  let l := (List.range 12).filter (adjacent g i)
  have hn : l.Nodup := (List.nodup_range).filter _
  have hset : l.toFinset = (Finset.range 12).filter (fun j => adjacent g i j = true) := by
    ext j
    simp [l]
  rw [degree, List.countP_eq_length_filter, ← hset]
  exact (List.toFinset_card_of_nodup hn).symm

/-- Any missing edge of a triangle-free cubic target passes the search's
degree and triangle tests as long as the current graph is a subgraph. -/
private theorem canJoin_encoded {part full : Fin 12 → Fin 12 → Bool}
    (hsub : ∀ a b, part a b = true → full a b = true)
    (hdegree : ∀ a : Fin 12, degree (encode full) a.val = 3)
    (hsymm : ∀ a b, full a b = full b a)
    (htriangle : ∀ a b c, full a b = true → full b c = true → full c a = true → False)
    (u v : Fin 12) (hedge : full u v = true)
    (hmiss : part u v = false) (hmiss' : part v u = false) :
    canJoin (encode part) u.val v.val = true := by
  have hd : degree (encode part) v.val < 3 := by
    rw [← hdegree v, degree_eq_card, degree_eq_card]
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro j hj
      obtain ⟨hjlt, hjadj⟩ := Finset.mem_filter.mp hj
      let x : Fin 12 := ⟨j, Finset.mem_range.mp hjlt⟩
      exact Finset.mem_filter.mpr ⟨hjlt,
        (encoded_adj full v x).trans (hsub v x ((encoded_adj part v x).symm.trans hjadj))⟩
    · intro he
      have hf : u.val ∈ (Finset.range 12).filter
          (fun j => adjacent (encode full) v.val j = true) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.isLt,
          (encoded_adj full v u).trans ((hsymm v u).trans hedge)⟩
      rw [← he] at hf
      have hp := (Finset.mem_filter.mp hf).2
      rw [encoded_adj part v u, hmiss'] at hp
      cases hp
  have hcommon : ((encode part)[u.val]! &&& (encode part)[v.val]!) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    change (adjacent (encode part) u.val j && adjacent (encode part) v.val j) =
      (0 : Nat).testBit j
    by_cases hj : j < 12
    · let x : Fin 12 := ⟨j, hj⟩
      have hu := encoded_adj part u x
      have hv := encoded_adj part v x
      rw [hu, hv]
      simp only [Nat.zero_testBit, Bool.and_eq_false_iff]
      cases hn : part u x
      · exact Or.inl rfl
      · right
        cases hb : part v x
        · rfl
        · exact (htriangle u v x hedge (hsub v x hb)
            ((hsymm x u).trans (hsub u x hn))).elim
    · simp only [encoded_outside part u (Nat.le_of_not_gt hj), Bool.false_and,
        Nat.zero_testBit]
  simp only [canJoin, hd, decide_true, encoded_adj part u v, hmiss, hcommon,
    Bool.not_false, Bool.and_true, beq_self_eq_true]

/-- The state after processing all vertices below `u` and inspecting the
neighbors of `u` below `k`. -/
private def prefixEdges (edge : Fin 12 → Fin 12 → Bool) (u k : Nat) (a b : Fin 12) : Bool :=
  edge a b && decide (a.val < u ∨ b.val < u ∨
    (a.val = u ∧ b.val < k) ∨ (b.val = u ∧ a.val < k))

private theorem partial_step (edge : Fin 12 → Fin 12 → Bool)
    (hsym : ∀ a b, edge a b = edge b a) (u v : Fin 12) (huv : u.val < v.val) :
    (if edge u v then join (encode (prefixEdges edge u.val v.val)) u.val v.val
      else encode (prefixEdges edge u.val v.val)) =
      encode (prefixEdges edge u.val (v.val + 1)) := by
  classical
  have hn : u ≠ v := fun h => (Nat.ne_of_lt huv) (congrArg Fin.val h)
  have compare (a b : Fin 12) :
      (a.val < u.val ∨ b.val < u.val ∨ (a.val = u.val ∧ b.val < v.val + 1) ∨
        (b.val = u.val ∧ a.val < v.val + 1)) ↔
      (a.val < u.val ∨ b.val < u.val ∨ (a.val = u.val ∧ b.val < v.val) ∨
        (b.val = u.val ∧ a.val < v.val)) ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
    simp only [Fin.ext_iff]
    omega
  cases h : edge u v
  · simp only [Bool.false_eq_true, ite_false]
    congr 1
    funext a b
    by_cases hu : a = u ∧ b = v
    · obtain ⟨rfl, rfl⟩ := hu
      simp only [prefixEdges, h, Bool.false_and]
    by_cases hv : a = v ∧ b = u
    · obtain ⟨rfl, rfl⟩ := hv
      simp only [prefixEdges, hsym a b, h, Bool.false_and]
    have he := compare a b
    simp only [hu, hv, or_false] at he
    simp only [prefixEdges, he]
  · simp only [ite_true, join_encoded _ _ _ hn]
    congr 1
    funext a b
    by_cases hu : a = u ∧ b = v
    · obtain ⟨rfl, rfl⟩ := hu
      simp [prefixEdges, h]
    by_cases hv : a = v ∧ b = u
    · obtain ⟨rfl, rfl⟩ := hv
      simp [prefixEdges, hsym a b, h]
    have he := compare a b
    simp only [hu, hv, or_false] at he
    have hb : (a == u && b == v) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hb
      exact hu ⟨beq_iff_eq.mp ha, beq_iff_eq.mp hb⟩
    have hc : (a == v && b == u) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hb
      exact hv ⟨beq_iff_eq.mp ha, beq_iff_eq.mp hb⟩
    simp only [prefixEdges, he, hb, hc, Bool.or_false]

/-- Follow the branch prescribed by the edges to previously discovered
vertices, updating the adjacency matrix at each selected neighbor. -/
private theorem select_prefix (edge : Fin 12 → Fin 12 → Bool)
    (hsym : ∀ a b, edge a b = edge b a)
    (hdegree : ∀ a : Fin 12, degree (encode edge) a.val = 3)
    (htriangle : ∀ a b c, edge a b = true → edge b c = true → edge c a = true → False)
    (u : Fin 12) (k n left : Nat) (hu : u.val < k) (hk : k + n ≤ 12)
    (hlen : ((List.range' k n).filter (adjacent (encode edge) u.val)).length ≤ left) :
    let row := adjacent (encode edge) u.val
    let chosen := (List.range' k n).filter row
    Choices u.val (List.range' k n) (encode (prefixEdges edge u.val k)) left chosen ∧
      chosen.foldl (fun g v => join g u.val v) (encode (prefixEdges edge u.val k)) =
        encode (prefixEdges edge u.val (k + n)) := by
  induction n generalizing k left with
  | zero => simp [Choices]
  | succ n ih =>
    let v : Fin 12 := ⟨k, by omega⟩
    have hrow : adjacent (encode edge) u.val k = edge u v := encoded_adj edge u v
    have hstep := partial_step edge hsym u v hu
    change (if edge u v then join (encode (prefixEdges edge u.val k)) u.val k
      else encode (prefixEdges edge u.val k)) =
      encode (prefixEdges edge u.val (k + 1)) at hstep
    dsimp only
    rw [List.range'_succ] at hlen ⊢
    have hsum : (k + 1) + n = k + (n + 1) := by omega
    cases h : edge u v
    · simp only [hrow, h, List.filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true] at hlen ⊢
      simp only [h, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨hc, hf⟩ := ih (k + 1) left (by omega) (by omega) hlen
      rw [hsum] at hf
      rw [hstep]
      exact ⟨Or.inl hc, hf⟩
    · simp only [hrow, h, List.filter_cons_of_pos, List.length_cons] at hlen ⊢
      simp only [h, ite_true] at hstep
      obtain ⟨hc, hf⟩ := ih (k + 1) (left - 1) (by omega) (by omega) (by omega)
      have hmiss : prefixEdges edge u.val k u v = false := by
        change (edge u v && decide (u.val < u.val ∨ k < u.val ∨
          (u.val = u.val ∧ k < k) ∨ (k = u.val ∧ u.val < k))) = false
        simp [Nat.not_lt_of_ge hu.le, Nat.ne_of_gt hu]
      have hmiss' : prefixEdges edge u.val k v u = false := by
        change (edge v u && decide (k < u.val ∨ u.val < u.val ∨
          (k = u.val ∧ u.val < k) ∨ (u.val = u.val ∧ k < k))) = false
        simp [Nat.not_lt_of_ge hu.le, Nat.ne_of_gt hu]
      have hj := canJoin_encoded (part := prefixEdges edge u.val k) (full := edge)
        (fun a b hab => (Bool.and_eq_true_iff.mp hab).1) hdegree hsym htriangle u v h hmiss hmiss'
      constructor
      · rw [Choices]
        rw [← hstep] at hc
        exact Or.inr ⟨by omega, hj, _, rfl, hc⟩
      · rw [List.foldl_cons, hstep, ← hsum]
        exact hf

private theorem range_split {a b : Nat} (h : a ≤ b) :
    List.range a ++ List.range' a (b - a) = List.range b := by
  calc
    List.range a ++ List.range' a (b - a) =
        List.range' 0 a ++ List.range' (0 + a) (b - a) := by
      rw [List.range_eq_range', Nat.zero_add]
    _ = List.range b := by rw [List.range'_append_1, Nat.add_sub_of_le h, List.range_eq_range']

private theorem degree_prefix (edge : Fin 12 → Fin 12 → Bool)
    (u : Fin 12) {k : Nat} (hu : u.val ≤ k) (hk : k ≤ 12) :
    degree (encode (prefixEdges edge u.val k)) u.val =
      (List.range k).countP (adjacent (encode edge) u.val) := by
  have row (j : Nat) (hj : j < 12) :
      adjacent (encode (prefixEdges edge u.val k)) u.val j =
        (adjacent (encode edge) u.val j && decide (j < k)) := by
    let v : Fin 12 := ⟨j, hj⟩
    have hp := encoded_adj (prefixEdges edge u.val k) u v
    have hf := encoded_adj edge u v
    change adjacent (encode (prefixEdges edge u.val k)) u.val j =
      prefixEdges edge u.val k u v at hp
    change adjacent (encode edge) u.val j = edge u v at hf
    rw [hp, hf]
    have he : (u.val < u.val ∨ j < u.val ∨ (True ∧ j < k) ∨
      (j = u.val ∧ u.val < k)) ↔ j < k := by
      simp only [true_and]
      omega
    change (edge u v && decide (u.val < u.val ∨ j < u.val ∨
      (u.val = u.val ∧ j < k) ∨ (j = u.val ∧ u.val < k))) = (edge u v && decide (j < k))
    simp only [he]
  rw [degree, ← range_split hk, List.countP_append]
  have hprefix : (List.range k).countP (adjacent (encode (prefixEdges edge u.val k)) u.val) =
      (List.range k).countP (adjacent (encode edge) u.val) := by
    apply List.countP_congr
    intro j hj
    have hjk := List.mem_range.mp hj
    simp only [row j (hjk.trans_le hk), hjk, decide_true, Bool.and_true]
  have hrest : (List.range' k (12 - k)).countP
      (adjacent (encode (prefixEdges edge u.val k)) u.val) = 0 := by
    apply List.countP_eq_zero.mpr
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hj
    have hjlt : k + 1 * i < 12 := by omega
    have hn : ¬ k + 1 * i < k := by omega
    simp only [row _ hjlt, hn, decide_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]
  rw [hprefix, hrest, Nat.add_zero]

private theorem advance_prefix (edge : Fin 12 → Fin 12 → Bool)
    (hsym : ∀ a b, edge a b = edge b a)
    (hloop : ∀ a, edge a a = false)
    (hdegree : ∀ a : Fin 12, degree (encode edge) a.val = 3)
    (htriangle : ∀ a b c, edge a b = true → edge b c = true → edge c a = true → False)
    (u : Fin 12) (discovered next : Nat) (hu : u.val < discovered)
    (hd : discovered ≤ next) (hn : next ≤ 12)
    (hnew : ∀ v : Fin 12, discovered ≤ v.val → (edge u v = true ↔ v.val < next)) :
    let available := List.range' (u.val + 1) (discovered - (u.val + 1))
    let chosen := available.filter (adjacent (encode edge) u.val)
    let graph := encode (prefixEdges edge u.val (u.val + 1))
    let left := 3 - degree graph u.val
    Choices u.val available graph left chosen ∧
      discovered + (left - chosen.length) = next ∧
      extendWith u.val discovered graph left chosen =
        (encode (prefixEdges edge (u.val + 1) (u.val + 2)), next) := by
  let row := adjacent (encode edge) u.val
  let available := List.range' (u.val + 1) (discovered - (u.val + 1))
  let chosen := available.filter row
  let graph := encode (prefixEdges edge u.val (u.val + 1))
  let left := 3 - degree graph u.val
  let fresh := List.range' discovered (next - discovered)
  have hrow {j : Nat} (hj : j < 12) (hj' : discovered ≤ j) :
      row j = true ↔ j < next := by
    let v : Fin 12 := ⟨j, hj⟩
    have he : row j = edge u v := encoded_adj edge u v
    rw [he]
    exact hnew v hj'
  have hfresh : fresh.filter row = fresh := by
    apply List.filter_eq_self.mpr
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hj
    exact (hrow (by omega) (by omega)).mpr (by omega)
  have hzero : (List.range' next (12 - next)).countP row = 0 := by
    apply List.countP_eq_zero.mpr
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hj
    exact fun hh => by have := (hrow (by omega) (by omega)).mp hh; omega
  have hcount := hdegree u
  change (List.range 12).countP row = 3 at hcount
  rw [← range_split hn, List.countP_append, hzero, Nat.add_zero,
    ← range_split hd, List.countP_append] at hcount
  change (List.range discovered).countP row + fresh.countP row = 3 at hcount
  rw [← range_split (Nat.succ_le_of_lt hu), List.countP_append,
    ← degree_prefix edge u (by omega) (by omega : u.val + 1 ≤ 12),
    List.countP_eq_length_filter, List.countP_eq_length_filter, hfresh,
    show fresh.length = next - discovered by simp [fresh]] at hcount
  change degree graph u.val + chosen.length + (next - discovered) = 3 at hcount
  have hleft : left - chosen.length = next - discovered := by
    dsimp only [left]
    omega
  have hselect := select_prefix edge hsym hdegree htriangle u (u.val + 1)
    (discovered - (u.val + 1)) left (by omega) (by omega) (by
      change chosen.length ≤ left
      dsimp only [left]
      omega)
  obtain ⟨hchoices, hold⟩ := hselect
  have hold' : chosen.foldl (fun g v => join g u.val v) graph =
      encode (prefixEdges edge u.val discovered) := by
    simpa only [Nat.add_sub_of_le (Nat.succ_le_of_lt hu)] using hold
  obtain ⟨_, hf⟩ := select_prefix edge hsym hdegree htriangle u discovered (next - discovered)
    (next - discovered) hu (by omega) (by
      change (fresh.filter row).length ≤ _
      rw [hfresh, List.length_range'])
  have hf' : fresh.foldl (fun g v => join g u.val v) (encode (prefixEdges edge u.val discovered)) =
      encode (prefixEdges edge u.val next) := by
    change (fresh.filter row).foldl (fun g v => join g u.val v)
      (encode (prefixEdges edge u.val discovered)) =
        encode (prefixEdges edge u.val (discovered + (next - discovered))) at hf
    rw [hfresh, Nat.add_sub_of_le hd] at hf
    exact hf
  have he : prefixEdges edge u.val next = prefixEdges edge (u.val + 1) (u.val + 2) := by
    funext a b
    cases hab : edge a b
    · simp only [prefixEdges, hab, Bool.false_and]
    · have hne : a ≠ b := by
        rintro rfl
        rw [hloop] at hab
        cases hab
      have hval : a.val ≠ b.val := fun h => hne (Fin.ext h)
      have ha : a.val = u.val → b.val < next := by
        intro h
        have e : a = u := Fin.ext h
        subst a
        by_cases hlt : b.val < discovered
        · exact hlt.trans_le hd
        · exact (hnew b (Nat.le_of_not_gt hlt)).mp hab
      have hb : b.val = u.val → a.val < next := by
        intro h
        have e : b = u := Fin.ext h
        subst b
        by_cases hlt : a.val < discovered
        · exact hlt.trans_le hd
        · exact (hnew a (Nat.le_of_not_gt hlt)).mp ((hsym u a).trans hab)
      simp only [prefixEdges, hab, Bool.true_and, decide_eq_decide]
      omega
  change Choices u.val available graph left chosen ∧ discovered + (left - chosen.length) = next ∧
    extendWith u.val discovered graph left chosen =
      (encode (prefixEdges edge (u.val + 1) (u.val + 2)), next)
  refine ⟨hchoices, by omega, ?_⟩
  change ((List.range' discovered (left - chosen.length)).foldl (fun g v => join g u.val v)
      (chosen.foldl (fun g v => join g u.val v) graph),
      discovered + (List.range' discovered (left - chosen.length)).length) = _
  rw [hold', hleft, List.length_range', Nat.add_sub_of_le hd]
  change (fresh.foldl (fun g v => join g u.val v)
    (encode (prefixEdges edge u.val discovered)), next) = _
  rw [hf', he]

private theorem follows_order (edge : Fin 12 → Fin 12 → Bool)
    (hsym : ∀ a b, edge a b = edge b a) (hloop : ∀ a, edge a a = false)
    (hdegree : ∀ a : Fin 12, degree (encode edge) a.val = 3)
    (htriangle : ∀ a b c, edge a b = true → edge b c = true → edge c a = true → False)
    (seen : Nat → Nat) (hinit : seen 0 = 1)
    (hmono : ∀ i, seen i ≤ seen (i + 1))
    (hsize : ∀ i, seen i ≤ 12)
    (hvertex : ∀ i < 12, i < seen i)
    (hnew : ∀ u v : Fin 12, seen u.val ≤ v.val →
      (edge u v = true ↔ v.val < seen (u.val + 1))) :
    encode edge ∈ candidates := by
  have follow (fuel vertex : Nat) (h : vertex + fuel = 12) :
      FollowsDiscovery fuel vertex (seen vertex)
        (encode (prefixEdges edge vertex (vertex + 1))) (encode edge) := by
    induction fuel generalizing vertex with
    | zero =>
      have hv : vertex = 12 := by omega
      subst vertex
      change encode edge = encode (prefixEdges edge 12 13)
      congr 1
      funext a b
      simp [prefixEdges, a.isLt]
    | succ fuel ih =>
      have hv : vertex < 12 := by omega
      let u : Fin 12 := ⟨vertex, hv⟩
      let available := List.range' (vertex + 1) (seen vertex - (vertex + 1))
      let chosen := available.filter (adjacent (encode edge) vertex)
      let graph := encode (prefixEdges edge vertex (vertex + 1))
      let left := 3 - degree graph vertex
      obtain ⟨hc, hn, hr⟩ := advance_prefix edge hsym hloop hdegree htriangle
        u (seen vertex) (seen (vertex + 1)) (hvertex vertex hv) (hmono vertex)
        (hsize (vertex + 1)) (hnew u)
      change Choices vertex available graph left chosen at hc
      change seen vertex + (left - chosen.length) = seen (vertex + 1) at hn
      change extendWith vertex (seen vertex) graph left chosen =
        (encode (prefixEdges edge (vertex + 1) (vertex + 2)), seen (vertex + 1)) at hr
      refine ⟨hvertex vertex hv, chosen, hc, ?_, ?_⟩
      · change seen vertex + (left - chosen.length) ≤ 12
        exact hn.trans_le (hsize (vertex + 1))
      · change FollowsDiscovery fuel (vertex + 1)
          (extendWith vertex (seen vertex) graph left chosen).2
          (extendWith vertex (seen vertex) graph left chosen).1 (encode edge)
        rw [hr]
        exact ih (vertex + 1) (by omega)
  have hfirst : prefixEdges edge 0 1 = fun _ _ => false := by
    funext a b
    by_cases ha : a.val = 0
    · by_cases hb : b.val = 0
      · have he : a = b := Fin.ext (ha.trans hb.symm)
        subst b
        simp [prefixEdges, hloop]
      · simp [prefixEdges, ha, hb]
    · by_cases hb : b.val = 0 <;> simp [prefixEdges, ha, hb]
  have hzero : encode (fun _ _ => false) = Array.replicate 12 0 := by decide
  have hm := follow 12 0 rfl
  rw [hinit, hfirst, hzero] at hm
  exact mem_search hm

private theorem degree_label {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (label : Fin 12 ≃ V) (i : Fin 12) :
    degree (encode (fun a b => decide (G.Adj (label a) (label b)))) i.val =
      G.degree (label i) := by
  classical
  let edge : Fin 12 → Fin 12 → Bool := fun a b => decide (G.Adj (label a) (label b))
  let row := adjacent (encode edge) i.val
  change degree (encode edge) i.val = G.degree (label i)
  rw [degree_eq_card, ← G.card_neighborFinset_eq_degree]
  change ((Finset.range 12).filter fun j => row j = true).card = _
  have bound (j : Nat) (hj : j ∈ (Finset.range 12).filter (fun j => row j = true)) :
      j < 12 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  refine Finset.card_bij (fun j hj => label ⟨j, bound j hj⟩) ?_ ?_ ?_
  · intro j hj
    have he : row j = edge i ⟨j, bound j hj⟩ := encoded_adj edge i ⟨j, bound j hj⟩
    exact (G.mem_neighborFinset _ _).mpr
      (of_decide_eq_true (he.symm.trans (Finset.mem_filter.mp hj).2))
  · intro j hj k hk h
    exact congrArg Fin.val (label.injective h)
  · intro v hv
    let j := label.symm v
    have hAdj : G.Adj (label i) (label j) := by
      simpa only [j, Equiv.apply_symm_apply] using (G.mem_neighborFinset _ _).mp hv
    refine ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, ?_⟩, ?_⟩
    · exact (encoded_adj edge i j).trans (decide_eq_true hAdj)
    · exact label.apply_symm_apply v

/-- The discovery order of every connected triangle-free cubic graph on
twelve vertices occurs in the finite search. -/
private theorem classify_graph {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = 12) (hconn : G.Connected)
    (hregular : G.IsRegularOfDegree 3)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (start : V) :
    ∃ label : Fin 12 ≃ V,
      encode (fun a b => decide (G.Adj (label a) (label b))) ∈ candidates := by
  classical
  let labels := discoveryLabels G hconn start
  let label : Fin 12 ≃ V := (Fin.castOrderIso hcard.symm).toEquiv.trans labels
  let seen (i : Nat) := (seenAfter G start i).length
  let edge (a b : Fin 12) := decide (G.Adj (label a) (label b))
  refine ⟨label, follows_order edge ?_ ?_ ?_ ?_ seen rfl ?_ ?_ ?_ ?_⟩
  · intro a b
    simp only [edge, G.adj_comm]
  · intro a
    simp [edge]
  · intro a
    exact (degree_label G label a).trans (hregular (label a))
  · intro a b c hab hbc hca
    exact htriangle _ _ _ (of_decide_eq_true hab) (of_decide_eq_true hbc)
      (of_decide_eq_true hca)
  · intro i
    exact (seen_prefix G start (Nat.le_succ i)).length_le
  · intro i
    have he := List.toFinset_card_of_nodup (seenAfter_nodup G start i)
    exact he.symm.trans_le ((Finset.card_le_univ _).trans_eq hcard)
  · intro i hi
    exact still_available G hconn start (hi.trans_eq hcard.symm)
  · intro a b hb
    have hf := new_neighbors_contiguous G hconn start (Fin.cast hcard.symm a)
      (Fin.cast hcard.symm b) hb
    change G.Adj (label a) (label b) ↔ b.val < seen (a.val + 1) at hf
    exact decide_eq_true_iff.trans hf

private theorem eraseDups_spec (xs : List Nat) :
    List.Sublist xs.eraseDups xs ∧ xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons]
    let tail := xs.filter (fun y => !y == x)
    obtain ⟨hsub, hn⟩ := eraseDups_spec tail
    refine ⟨(hsub.trans List.filter_sublist).cons₂ _, List.nodup_cons.mpr ⟨?_, hn⟩⟩
    intro hx
    have hf := (List.mem_filter.mp (List.mem_eraseDups.mp hx)).2
    simp at hf
termination_by xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private noncomputable def witnessPerm (word : Nat) (hb : ∀ i < 12, labels word i < 12)
    (hn : ((List.range 12).map (labels word)).eraseDups.length = 12) : Equiv.Perm (Fin 12) := by
  let f := fun i : Fin 12 => (⟨labels word i.val, hb i.val i.isLt⟩ : Fin 12)
  let l := (List.range 12).map (labels word)
  have spec := eraseDups_spec l
  have hlen : l.length = 12 := by simp [l]
  have hself := spec.1.length_eq.mp (hn.trans hlen.symm)
  have hnd : l.Nodup := hself ▸ spec.2
  have hi := (List.nodup_map_iff_inj_on List.nodup_range).mp hnd
  have injective : Function.Injective f := by
    intro a b e
    apply Fin.ext
    exact hi _ (List.mem_range.mpr a.isLt) _ (List.mem_range.mpr b.isLt) (congrArg Fin.val e)
  exact Equiv.ofBijective f ⟨injective, Finite.surjective_of_injective injective⟩

/-- One of the 22 table entries represents any connected triangle-free cubic
graph on twelve vertices, with a bijection preserving every adjacency. -/
private theorem representative_of_graph {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = 12) (hconn : G.Connected)
    (hregular : G.IsRegularOfDegree 3)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False) (start : V) :
    ∃ (index : Fin 22) (label : Fin 12 ≃ V), ∀ i j,
      adjacent (decode representatives[index.val]!) i.val j.val = true ↔
        G.Adj (label i) (label j) := by
  obtain ⟨number, hnum⟩ := classify_graph G hcard hconn hregular htriangle start
  let edge : Fin 12 → Fin 12 → Bool := fun i j => decide (G.Adj (number i) (number j))
  obtain ⟨word, hw⟩ := candidate_has_witness hnum
  let index := word >>> 48
  change ((decide (index < representatives.size) &&
    (List.range 12).all (fun i => decide (labels word i < 12)) &&
    (((List.range 12).map (labels word)).eraseDups.length == 12)) &&
    (List.range 12).all (fun i => (List.range 12).all fun j => adjacent (encode edge) i j ==
      adjacent (decode representatives[index]!) (labels word i) (labels word j))) = true at hw
  obtain ⟨⟨⟨hindex, hbound⟩, hnodup⟩, hmatrix⟩ := by
    simpa only [Bool.and_eq_true_iff] using hw
  let p := witnessPerm word (fun i hi =>
    of_decide_eq_true (List.all_eq_true.mp hbound _ (List.mem_range.mpr hi)))
    (beq_iff_eq.mp hnodup)
  have hr : representatives.size = 22 := rfl
  let idx : Fin 22 := ⟨index, hr ▸ of_decide_eq_true hindex⟩
  refine ⟨idx, p.symm.trans number, fun i j => ?_⟩
  let a := p.symm i
  let b := p.symm j
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp hmatrix _ (List.mem_range.mpr a.isLt)) _
    (List.mem_range.mpr b.isLt)
  have ha : labels word a.val = i.val := congrArg Fin.val (p.apply_symm_apply i)
  have hb : labels word b.val = j.val := congrArg Fin.val (p.apply_symm_apply j)
  have he := beq_iff_eq.mp h
  rw [ha, hb, encoded_adj edge a b] at he
  change adjacent (decode representatives[index]!) i.val j.val = true ↔
    G.Adj (number a) (number b)
  rw [← he]
  exact decide_eq_true_iff

#print axioms join_encoded
#print axioms canJoin_encoded
#print axioms partial_step
#print axioms select_prefix
#print axioms degree_prefix
#print axioms advance_prefix
#print axioms follows_order
#print axioms classify_graph
#print axioms representative_of_graph

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding
