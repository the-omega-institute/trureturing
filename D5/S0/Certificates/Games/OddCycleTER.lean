/- GID: D5/S0/Certificates/Games/OddCycleTER
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/OddCycleTER
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: The original graph game TERMINATE has initial Grundy value zero on every odd cycle of length at least five. -/

import D5.S0.Certificates.Games.CrimGrundyRefutation
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric

open Finset
namespace OddCycleTER

abbrev Vertex (m : ℕ) := Fin (2 * m + 1)

/-- Clockwise length in edges, with zero for coincident endpoints. -/
private def cw {n : ℕ} (x y : Fin n) : ℕ := (y - x).val

private theorem cw_lt {n : ℕ} (x y : Fin n) : cw x y < n := (y - x).isLt

@[simp] private theorem cw_self {n : ℕ} [NeZero n] (x : Fin n) : cw x x = 0 := by
  simp [cw]

private theorem cw_injective {n : ℕ} [NeZero n] (x : Fin n) : Function.Injective (cw x) := by
  intro y z h
  exact (Equiv.subRight x).injective (Fin.ext h)

private theorem cw_pos {n : ℕ} [NeZero n] {x y : Fin n} (h : x ≠ y) : 0 < cw x y := by
  exact Nat.pos_of_ne_zero (fun he => h ((cw_injective x) (he.trans (cw_self x).symm)).symm)

/-- Changing the origin subtracts the two old coordinates modulo the cycle length. -/
private theorem cw_change {n : ℕ} [NeZero n] (a x y : Fin n) :
    cw x y = if cw a x ≤ cw a y then cw a y - cw a x else n + cw a y - cw a x := by
  have h : y - x = (y - a) - (x - a) := by
    rw [sub_sub_sub_cancel_right]
  change (y - x).val = if (x-a).val ≤ (y-a).val then
    (y-a).val - (x-a).val else n + (y-a).val - (x-a).val
  conv_lhs => rw [h]
  split
  · rename_i hle
    exact Fin.sub_val_of_le hle
  · rename_i hle
    change ((n - (x-a).val) + (y-a).val) % n = _
    have := (x - a).isLt
    have := (y - a).isLt
    have hsmall : (n - (x-a).val) + (y-a).val < n := by omega
    rw [Nat.mod_eq_of_lt hsmall]
    omega

/-- The survivors strictly inside the clockwise arc from x to y. -/
private def interior {n : ℕ} (R : Finset (Fin n)) (x y : Fin n) : Finset (Fin n) :=
  R.filter (fun z => 0 < cw x z ∧ cw x z < cw x y)

private theorem reverse_interior_iff {n : ℕ} [NeZero n] {x y z : Fin n} (hxy : x ≠ y) :
    (0 < cw y z ∧ cw y z < cw y x) ↔ cw x y < cw x z := by
  have hp := cw_pos hxy
  have hy := cw_lt x y
  have hz := cw_lt x z
  have hnot : ¬ cw x y ≤ 0 := by omega
  rw [cw_change x y z, cw_change x y x, cw_self]
  simp only [hnot, ↓reduceIte, Nat.add_zero]
  split <;> omega

/-- Rank k after x, numbered from one, gives the two strict arc counts. -/
private theorem kth_survivor_arcs {n : ℕ} [NeZero n] (R : Finset (Fin n))
    {x : Fin n} (hx : x ∈ R) {k : ℕ} (hk : 0 < k) (hR : R.card = 2*k+1) :
    ∃ y ∈ R.erase x, (interior R x y).card = k-1 ∧ (interior R y x).card = k := by
  let shift : Fin n ≃ Fin n := Equiv.subRight x
  let A := (R.erase x).map shift.toEmbedding
  have hA : A.card = 2*k := by
    rw [card_map, card_erase_of_mem hx, hR]
    omega
  let e := A.orderEmbOfFin hA
  let i : Fin (2*k) := ⟨k-1, by omega⟩
  let y := shift.symm (e i)
  have ha : ∀ j, shift.symm (e j) ∈ R.erase x := by
    intro j
    have hj : e j ∈ A := A.orderEmbOfFin_mem hA j
    obtain ⟨z, hz, he⟩ := mem_map.mp hj
    change shift z = e j at he
    simpa [← he] using hz
  have hrank : ∀ z ∈ R.erase x, ∃ j, shift.symm (e j) = z := by
    intro z hz
    have hz' : shift z ∈ A := mem_map.mpr ⟨z, hz, rfl⟩
    have hz'' : shift z ∈ Set.range e := by
      rw [A.range_orderEmbOfFin hA]
      exact hz'
    obtain ⟨j, hj⟩ := hz''
    exact ⟨j, by rw [hj, Equiv.symm_apply_apply]⟩
  let f : Fin (2*k) ↪ Fin n := e.toEmbedding.trans shift.symm.toEmbedding
  have hf : ∀ j, cw x (f j) = (e j).val := by
    intro j
    change (shift (shift.symm (e j))).val = _
    rw [Equiv.apply_symm_apply]
  have hy : y ∈ R.erase x := ha i
  have hxy : x ≠ y := (mem_erase.mp hy).1.symm
  have hlt : ∀ j, cw x (f j) < cw x y ↔ j < i := by
    intro j
    change cw x (f j) < cw x (f i) ↔ j < i
    rw [hf, hf]
    exact e.lt_iff_lt
  have hgt : ∀ j, cw x y < cw x (f j) ↔ i < j := by
    intro j
    change cw x (f i) < cw x (f j) ↔ i < j
    rw [hf, hf]
    exact e.lt_iff_lt
  have hleft : interior R x y = (Iio i).map f := by
    ext z
    simp only [interior, mem_filter, mem_map, mem_Iio]
    constructor
    · rintro ⟨hz, hp, hl⟩
      have hzx : z ≠ x := by rintro rfl; simp at hp
      obtain ⟨j, hj⟩ := hrank z (mem_erase.mpr ⟨hzx, hz⟩)
      change f j = z at hj
      exact ⟨j, (hlt j).mp (hj ▸ hl), hj⟩
    · rintro ⟨j, hj, rfl⟩
      have hj' := mem_erase.mp (ha j)
      exact ⟨hj'.2, cw_pos hj'.1.symm, (hlt j).mpr hj⟩
  have hright : interior R y x = (Ioi i).map f := by
    ext z
    simp only [interior, mem_filter, reverse_interior_iff hxy, mem_map, mem_Ioi]
    constructor
    · rintro ⟨hz, hl⟩
      have hzx : z ≠ x := by rintro rfl; simp at hl
      obtain ⟨j, hj⟩ := hrank z (mem_erase.mpr ⟨hzx, hz⟩)
      change f j = z at hj
      exact ⟨j, (hgt j).mp (hj ▸ hl), hj⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(mem_erase.mp (ha j)).2, (hgt j).mpr hj⟩
  refine ⟨y, hy, ?_, ?_⟩
  · rw [hleft, card_map, Fin.card_Iio]
  · rw [hright, card_map, Fin.card_Ioi]
    change 2*k-1-(k-1) = k
    omega

private def block {n : ℕ} (m : ℕ) (a : Fin n) : Finset (Fin n) :=
  univ.filter (fun z => cw a z < m)

@[simp] private theorem mem_block {n m : ℕ} {a z : Fin n} : z ∈ block m a ↔ cw a z < m := by
  simp [block]

/-- A consecutive block containing both endpoints contains the whole intervening arc
when the endpoints are in increasing order in the block's coordinates. -/
private theorem interior_subset_block {n m : ℕ} [NeZero n] {R : Finset (Fin n)} {a x y : Fin n}
    (h : cw a x ≤ cw a y) (hy : y ∈ block m a) :
    interior R x y ⊆ R ∩ block m a := by
  intro z hz
  obtain ⟨hzR, hp, hl⟩ := mem_filter.mp hz
  refine mem_inter.mpr ⟨hzR, mem_block.mpr ?_⟩
  have hx := cw_lt a x
  have hyy := cw_lt a y
  rw [cw_change a x y, cw_change a x z] at hl
  simp only [h, ↓reduceIte] at hl
  have hb := mem_block.mp hy
  split at hl <;> omega

private theorem block_card_ge_interior_add_two {n m : ℕ} [NeZero n]
    {R : Finset (Fin n)} {a x y : Fin n} (hxy : x ≠ y) (hx : x ∈ R) (hy : y ∈ R)
    (h : cw a x ≤ cw a y) (hxb : x ∈ block m a) (hyb : y ∈ block m a) :
    (interior R x y).card + 2 ≤ (R ∩ block m a).card := by
  have hxI : x ∉ interior R x y := by simp [interior]
  have hyI : y ∉ interior R x y := by simp [interior]
  have hs : insert x (insert y (interior R x y)) ⊆ R ∩ block m a :=
    insert_subset (mem_inter.mpr ⟨hx, hxb⟩)
      (insert_subset (mem_inter.mpr ⟨hy, hyb⟩) (interior_subset_block h hyb))
  have hc := card_le_card hs
  rw [card_insert_of_notMem (by simp [hxy, hxI]), card_insert_of_notMem hyI] at hc
  exact hc

/-- The two specified endpoints cannot both lie in a block with exactly k survivors. -/
private theorem exact_block_excludes_endpoints {n m k : ℕ} [NeZero n]
    {R : Finset (Fin n)} {a x y : Fin n}
    (hk : 0 < k) (hx : x ∈ R) (hy : y ∈ R.erase x)
    (hl : (interior R x y).card = k-1) (hr : (interior R y x).card = k)
    (hcard : (R ∩ block m a).card = k) :
    ¬ (x ∈ block m a ∧ y ∈ block m a) := by
  have hxy := (mem_erase.mp hy).1.symm
  have hyR := (mem_erase.mp hy).2
  rintro ⟨hxb, hyb⟩
  rcases le_total (cw a x) (cw a y) with h | h
  · have := block_card_ge_interior_add_two hxy hx hyR h hxb hyb
    omega
  · have := block_card_ge_interior_add_two hxy.symm hyR hx h hyb hxb
    omega


private def Invariant (k : ℕ) (R : Finset (Vertex m)) : Prop :=
  R.card = 2*k+1 ∧ ∀ a, k ≤ (R ∩ block m a).card

private def BlockLive (R : Finset (Vertex m)) : Prop :=
  ∀ a, (R ∩ block m a).Nonempty

private theorem first_erase_live {k : ℕ} {R : Finset (Vertex m)} (hk : 2 ≤ k)
    (h : Invariant k R) (x : Vertex m) : BlockLive (R.erase x) := by
  intro a
  apply card_pos.mp
  rw [Finset.erase_inter]
  have hc := pred_card_le_card_erase (s := R ∩ block m a) (a := x)
  have hb := h.2 a
  omega

private theorem rank_reply {k : ℕ} {R : Finset (Vertex m)} (hk : 2 ≤ k)
    (h : Invariant k R) {x : Vertex m} (hx : x ∈ R) :
    ∃ y ∈ R.erase x, Invariant (k-1) ((R.erase x).erase y) := by
  obtain ⟨y, hy, hl, hr⟩ := kth_survivor_arcs R hx (by omega) h.1
  refine ⟨y, hy, ?_, ?_⟩
  · rw [card_erase_of_mem hy, card_erase_of_mem hx, h.1]
    omega
  · intro a
    rw [Finset.erase_inter, Finset.erase_inter]
    have hb := h.2 a
    let B := R ∩ block m a
    change k ≤ B.card at hb
    change k-1 ≤ ((B.erase x).erase y).card
    have h1 := pred_card_le_card_erase (s := B) (a := x)
    have h2 := pred_card_le_card_erase (s := B.erase x) (a := y)
    by_cases he : B.card = k
    · have hnot := exact_block_excludes_endpoints (a := a) (m := m) (by omega) hx hy hl hr he
      by_cases hxb : x ∈ block m a
      · have hyb : y ∉ B.erase x := by
          intro hy'
          exact hnot ⟨hxb, (mem_inter.mp (mem_of_mem_erase hy')).2⟩
        rw [erase_eq_of_notMem hyb]
        omega
      · have hxB : x ∉ B := fun hx' => hxb (mem_inter.mp hx').2
        rw [erase_eq_of_notMem hxB] at h2 ⊢
        omega
    · omega

private theorem cw_add_offset {n : ℕ} [NeZero n] (x : Fin n) {j : ℕ} (hj : j < n) :
    cw x (x + Fin.ofNat n j) = j := by
  unfold cw
  rw [add_comm, add_sub_cancel_right, Fin.val_ofNat, Nat.mod_eq_of_lt hj]

private theorem block_offset {m j : ℕ} (x z : Vertex m) (hj : j < 2*m+1)
    (hjm : j + m ≤ 2*m+1) :
    z ∈ block m (x + Fin.ofNat (2*m+1) j) ↔ j ≤ cw x z ∧ cw x z < j + m := by
  rw [mem_block, cw_change x, cw_add_offset x hj]
  split <;> omega

private theorem block_card {m : ℕ} (a : Vertex m) : (block m a).card = m := by
  let f : ℕ → Vertex m := fun j => a + Fin.ofNat (2*m+1) j
  have hinj : Set.InjOn f (↑(range m) : Set ℕ) := by
    intro i hi j hj he
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have h := congrArg (cw a) he
    change cw a (a + Fin.ofNat (2*m+1) i) = cw a (a + Fin.ofNat (2*m+1) j) at h
    rwa [cw_add_offset a (by omega), cw_add_offset a (by omega)] at h
  have he : block m a = (range m).image f := by
    ext z
    rw [mem_block, mem_image]
    constructor
    · intro hz
      refine ⟨cw a z, mem_range.mpr hz, ?_⟩
      apply cw_injective a
      exact cw_add_offset a (cw_lt a z)
    · rintro ⟨j, hj, rfl⟩
      have hj' := mem_range.mp hj
      exact (cw_add_offset a (by omega)).trans_lt hj'
  rw [he, card_image_of_injOn hinj, card_range]

private theorem initial_invariant (m : ℕ) : Invariant m (univ : Finset (Vertex m)) := by
  constructor
  · simp
  · intro a
    simp [block_card]

/-- A live four-survivor position has a block with exactly one survivor. -/
private theorem four_has_singleton_block {R : Finset (Vertex m)} (hR : R.card = 4)
    (hLive : BlockLive R) : ∃ a, (R ∩ block m a).card = 1 := by
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < R.card by omega)
  let a := z + Fin.ofNat (2*m+1) 1
  let b := z + Fin.ofNat (2*m+1) (m+1)
  have hm : 0 < m := by
    have h := card_le_univ R
    rw [Fintype.card_fin] at h
    omega
  have ha : ∀ w : Vertex m, w ∈ block m a ↔ 1 ≤ cw z w ∧ cw z w < m+1 := by
    intro w
    simpa [a, Nat.add_comm] using
      (block_offset (m := m) (j := 1) z w (by omega) (by omega))
  have hb : ∀ w : Vertex m, w ∈ block m b ↔ m+1 ≤ cw z w ∧ cw z w < 2*m+1 := by
    intro w
    convert block_offset (m := m) (j := m+1) z w (by omega) (by omega) using 2
    omega
  have hdis : Disjoint (R ∩ block m a) (R ∩ block m b) := by
    apply disjoint_left.mpr
    intro w hw hw'
    have h1 := (ha w).mp (mem_inter.mp hw).2
    have h2 := (hb w).mp (mem_inter.mp hw').2
    omega
  have hsub : (R ∩ block m a) ∪ (R ∩ block m b) ⊆ R.erase z := by
    intro w hw
    apply mem_erase.mpr
    rcases mem_union.mp hw with hw | hw
    · refine ⟨?_, (mem_inter.mp hw).1⟩
      intro he
      subst w
      simpa using ((ha z).mp (mem_inter.mp hw).2).1
    · refine ⟨?_, (mem_inter.mp hw).1⟩
      intro he
      subst w
      simpa using ((hb z).mp (mem_inter.mp hw).2).1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_erase_of_mem hz, hR] at hc
  have hpa := card_pos.mpr (hLive a)
  have hpb := card_pos.mpr (hLive b)
  by_cases h : (R ∩ block m a).card = 1
  · exact ⟨a, h⟩
  · exact ⟨b, by omega⟩

private theorem four_terminal_reply {R : Finset (Vertex m)} (hR : R.card = 4)
    (hLive : BlockLive R) : ∃ y ∈ R, ¬ BlockLive (R.erase y) := by
  obtain ⟨a, ha⟩ := four_has_singleton_block hR hLive
  obtain ⟨y, hy⟩ := card_eq_one.mp ha
  have hmem : y ∈ R ∩ block m a := by simp [hy]
  refine ⟨y, (mem_inter.mp hmem).1, fun h => ?_⟩
  have hne := h a
  rw [Finset.erase_inter, hy, erase_singleton] at hne
  exact not_nonempty_empty hne


open SimpleGraph

private theorem cw_step {n : ℕ} [NeZero n] (hn : 1 < n) (x : Fin n) :
    cw x (x + 1) = 1 := by
  unfold cw
  rw [add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt hn]

private theorem cycle_adj_iff {n : ℕ} {x y : Fin n} :
    (cycleGraph n).Adj x y ↔ cw x y = 1 ∨ cw y x = 1 := by
  simpa only [cw, or_comm] using (cycleGraph_adj' (u := x) (v := y))

private theorem cycle_walk_clockwise {n : ℕ} [NeZero n] (hn : 1 < n) (x y : Fin n) :
    ∃ p : (cycleGraph n).Walk x y, p.length = cw x y := by
  generalize ht : cw x y = t
  induction t generalizing x with
  | zero =>
    have he := cw_injective x (ht.trans (cw_self x).symm)
    subst y
    exact ⟨.nil, rfl⟩
  | succ t ih =>
    let u := x + 1
    have hs : cw x u = 1 := cw_step hn x
    have htu : cw u y = t := by
      rw [cw_change x u y, hs, ht]
      simp
    obtain ⟨p, hp⟩ := ih u htu
    exact ⟨.cons (cycle_adj_iff.mpr (Or.inl hs)) p, by simp [hp]⟩

private def cyclicDist {n : ℕ} (x y : Fin n) : ℕ := min (cw x y) (cw y x)

private theorem cyclicDist_coord {n : ℕ} [NeZero n] (x y : Fin n) :
    cyclicDist x y = min (cw x y) (n - cw x y) := by
  by_cases h : x = y
  · simp [h, cyclicDist]
  · have hp := cw_pos h
    have hnot : ¬ cw x y ≤ 0 := by omega
    unfold cyclicDist
    conv_lhs => arg 2; rw [cw_change x y x, cw_self]
    simp [hnot]

private theorem coordinate_step {n : ℕ} [NeZero n] {a u v : Fin n}
    (h : cw u v = 1) :
    cw a v = cw a u + 1 ∨ (cw a v = 0 ∧ cw a u + 1 = n) := by
  have hu := cw_lt a u
  have hv := cw_lt a v
  rw [cw_change a u v] at h
  split at h <;> omega

private theorem min_coord_step {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : j = i+1 ∨ (j = 0 ∧ i+1 = n)) :
    min i (n-i) ≤ min j (n-j)+1 ∧ min j (n-j) ≤ min i (n-i)+1 := by
  simp only [min_def]
  split <;> split <;> omega

private theorem cyclicDist_le_walk {n : ℕ} [NeZero n] {x y : Fin n}
    (p : (cycleGraph n).Walk x y) : cyclicDist x y ≤ p.length := by
  induction p with
  | nil => simp [cyclicDist]
  | @cons u v w h p ih =>
    have hstep : cyclicDist w u ≤ cyclicDist w v + 1 := by
      rw [cyclicDist_coord, cyclicDist_coord]
      rcases cycle_adj_iff.mp h with h | h
      · exact (min_coord_step (cw_lt w u) (cw_lt w v) (coordinate_step h)).1
      · exact (min_coord_step (cw_lt w v) (cw_lt w u) (coordinate_step h)).2
    have ih' : cyclicDist w v ≤ p.length := by simpa [cyclicDist, min_comm] using ih
    have hh := hstep.trans (Nat.add_le_add_right ih' 1)
    simpa [cyclicDist, min_comm] using hh

private theorem cycle_dist {n : ℕ} [NeZero n] (hn : 1 < n) (x y : Fin n) :
    (cycleGraph n).dist x y = cyclicDist x y := by
  obtain ⟨p, hp⟩ := cycle_walk_clockwise hn x y
  obtain ⟨q, hq⟩ := cycle_walk_clockwise hn y x
  obtain ⟨r, hr⟩ := p.reachable.exists_walk_length_eq_dist
  apply le_antisymm
  · exact le_min (hp ▸ dist_le p) (by simpa [hq] using dist_le q.reverse)
  · exact hr ▸ cyclicDist_le_walk r

/-- Convexity for all shortest walks in the original graph. A shortest walk is a path. -/
def GeoConvex {n : ℕ} (K : Set (Fin n)) : Prop :=
  ∀ ⦃x y : Fin n⦄, x ∈ K → y ∈ K →
    ∀ p : (cycleGraph n).Walk x y, p.length = (cycleGraph n).dist x y →
      ∀ ⦃z : Fin n⦄, z ∈ p.support → z ∈ K

private theorem geoConvex_iff_dist {n : ℕ} [NeZero n] (hn : 1 < n) (K : Set (Fin n)) :
    GeoConvex K ↔
    ∀ ⦃x y z : Fin n⦄, x ∈ K → y ∈ K →
      (cycleGraph n).dist x z + (cycleGraph n).dist z y = (cycleGraph n).dist x y → z ∈ K := by
  constructor
  · intro h x y z hx hy hz
    obtain ⟨p, hp⟩ := cycle_walk_clockwise hn x z
    obtain ⟨q, hq⟩ := cycle_walk_clockwise hn z y
    obtain ⟨p', hp'⟩ := p.reachable.exists_walk_length_eq_dist
    obtain ⟨q', hq'⟩ := q.reachable.exists_walk_length_eq_dist
    exact h hx hy (p'.append q') (by simpa [hp', hq'] using hz)
      ((Walk.mem_support_append_iff _ _).mpr (Or.inl p'.end_mem_support))
  · intro h x y hx hy p hp z hz
    obtain ⟨p₁, p₂, he⟩ := (p.mem_support_iff_exists_append).mp hz
    have hsum : p₁.length + p₂.length = p.length := by rw [← Walk.length_append, ← he]
    apply h hx hy
    apply le_antisymm
    · exact (Nat.add_le_add (dist_le p₁) (dist_le p₂)).trans (by omega)
    · exact p₁.reachable.dist_triangle_left y

def geoHull {n : ℕ} (R : Finset (Fin n)) : Set (Fin n) :=
  { z | ∀ K : Set (Fin n), (↑R : Set (Fin n)) ⊆ K → GeoConvex K → z ∈ K }

private theorem geoHull_subset {n : ℕ} {R : Finset (Fin n)} {K : Set (Fin n)}
    (hR : (↑R : Set (Fin n)) ⊆ K) (hK : GeoConvex K) : geoHull R ⊆ K :=
  fun _ hz => hz K hR hK

private theorem subset_geoHull {n : ℕ} (R : Finset (Fin n)) :
    (↑R : Set (Fin n)) ⊆ geoHull R :=
  fun _ hz _ hsub _ => hsub hz

private theorem geoHull_convex {n : ℕ} (R : Finset (Fin n)) : GeoConvex (geoHull R) :=
  by
    intro x y hx hy p hp z hz K hsub hK
    exact hK (hx K hsub hK) (hy K hsub hK) p hp hz


private theorem cyclicDist_of_coord_le {n : ℕ} [NeZero n] {a x y : Fin n}
    (h : cw a x ≤ cw a y) :
    cyclicDist x y = min (cw a y - cw a x) (n - (cw a y - cw a x)) := by
  rw [cyclicDist_coord, cw_change a x y]
  simp only [h, ↓reduceIte]

private theorem short_arc_convex (hm : 2 ≤ m) (a : Vertex m) : GeoConvex {z | cw a z ≤ m} := by
  apply (geoConvex_iff_dist (by omega) _).mpr
  intro x y z hx hy he
  change cw a x ≤ m at hx
  change cw a y ≤ m at hy
  change cw a z ≤ m
  by_contra hzb
  have hzn := cw_lt a z
  have aux : ∀ (u v : Vertex m), cw a u ≤ cw a v → cw a v ≤ m →
      (cycleGraph (2*m+1)).dist u z + (cycleGraph (2*m+1)).dist z v ≠
        (cycleGraph (2*m+1)).dist u v := by
    intro u v huv hv hc
    have h1 : cw a u ≤ cw a z := by omega
    have h2 : cw a v ≤ cw a z := by omega
    rw [dist_comm (u := z) (v := v), cycle_dist (by omega),
      cycle_dist (by omega), cycle_dist (by omega),
      cyclicDist_of_coord_le h1, cyclicDist_of_coord_le h2, cyclicDist_of_coord_le huv] at hc
    have hshort : cw a v - cw a u ≤ 2*m+1-(cw a v-cw a u) := by omega
    rw [min_eq_left hshort] at hc
    simp only [min_def] at hc
    split at hc <;> split at hc <;> omega
  rcases le_total (cw a x) (cw a y) with h | h
  · exact aux x y h hy he
  · apply aux y x h hx
    rw [dist_comm (u := y) (v := z), dist_comm (u := z) (v := x),
      dist_comm (u := y) (v := x), Nat.add_comm]
    exact he

private theorem block_complement_short_arc (a z : Vertex m) :
    z ∉ block m a ↔ cw (a + Fin.ofNat (2*m+1) m) z ≤ m := by
  rw [mem_block, cw_change a (a + Fin.ofNat (2*m+1) m) z,
    cw_add_offset a (by omega)]
  have h := cw_lt a z
  split <;> omega

private theorem geoHull_eq_univ_iff (R : Finset (Vertex m)) (hm : 2 ≤ m) :
    geoHull R = Set.univ ↔ BlockLive R := by
  constructor
  · intro h a
    by_contra hnone
    let b := a + Fin.ofNat (2*m+1) m
    have hs : (↑R : Set (Vertex m)) ⊆ {z | cw b z ≤ m} := by
      intro z hz
      apply (block_complement_short_arc a z).mp
      exact fun hz' => hnone ⟨z, mem_inter.mpr ⟨hz, hz'⟩⟩
    have hh := geoHull_subset hs (short_arc_convex hm b)
    have ha : a ∈ geoHull R := by simp [h]
    exact ((block_complement_short_arc a a).mpr (hh ha)) (by simp; omega)
  · intro h
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ R
    · exact subset_geoHull R hz
    let A := R.image (cw z)
    obtain ⟨w, hw⟩ := h z
    have hA : A.Nonempty := ⟨cw z w, mem_image_of_mem _ (mem_inter.mp hw).1⟩
    obtain ⟨l, hlR, hl⟩ := mem_image.mp (A.min'_mem hA)
    obtain ⟨u, huR, hu⟩ := mem_image.mp (A.max'_mem hA)
    have hlmin : ∀ w ∈ R, cw z l ≤ cw z w := by
      intro w hw
      rw [hl]
      exact A.min'_le _ (mem_image_of_mem _ hw)
    have humax : ∀ w ∈ R, cw z w ≤ cw z u := by
      intro w hw
      rw [hu]
      exact A.le_max' _ (mem_image_of_mem _ hw)
    have hpos : 0 < cw z l := cw_pos (fun he => hz (he ▸ hlR))
    have hhi := cw_lt z u
    have hlo := hlmin u huR
    have hgap : 2*m+1 - cw z u + cw z l ≤ m := by
      by_contra hgap
      obtain ⟨v, hv⟩ := h (u + Fin.ofNat (2*m+1) 1)
      obtain ⟨hvR, hvB⟩ := mem_inter.mp hv
      have hvmax := humax v hvR
      have hvmin := hlmin v hvR
      have hvcoord := (block_offset u v (j := 1) (by omega) (by omega)).mp hvB
      rw [cw_change z u v] at hvcoord
      split at hvcoord <;> omega
    have hlt : cw z l < cw z u := by omega
    have hcu : cw u z = 2*m+1 - cw z u := by
      rw [cw_change z u z, cw_self]
      have hnot : ¬ cw z u ≤ 0 := by omega
      simp [hnot]
    have hcul : cw u l = 2*m+1 - cw z u + cw z l := by
      rw [cw_change z u l]
      have hnot : ¬ cw z u ≤ cw z l := by omega
      simp only [hnot, ↓reduceIte]
      omega
    apply (geoConvex_iff_dist (by omega) _).mp (geoHull_convex R)
        (subset_geoHull R huR) (subset_geoHull R hlR)
    rw [cycle_dist (by omega), cycle_dist (by omega), cycle_dist (by omega),
        cyclicDist_coord, cyclicDist_coord, cyclicDist_coord, hcu, hcul]
    have h1 : 2*m+1 - cw z u ≤ 2*m+1-(2*m+1 - cw z u) := by omega
    have h2 : cw z l ≤ 2*m+1-cw z l := by omega
    have h3 : 2*m+1 - cw z u + cw z l ≤ 2*m+1-(2*m+1 - cw z u+cw z l) := by omega
    rw [min_eq_left h1, min_eq_left h2, min_eq_left h3]


/-- A move may delete any survivor of a live position. The destination can be terminal. -/
noncomputable def moves (R : Finset (Vertex m)) : Finset (Finset (Vertex m)) := by
  classical
  exact if geoHull R = Set.univ then R.image R.erase else ∅

theorem mem_moves {R Q : Finset (Vertex m)} :
    Q ∈ moves R ↔ geoHull R = Set.univ ∧ ∃ x ∈ R, R.erase x = Q := by
  classical
  by_cases h : geoHull R = Set.univ <;> simp [moves, h]

private theorem move_card_lt {R Q : Finset (Vertex m)} (h : Q ∈ moves R) :
    Q.card < R.card := by
  obtain ⟨_, x, hx, rfl⟩ := mem_moves.mp h
  exact card_lt_card (erase_ssubset hx)

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

/-- The Sprague–Grundy recurrence on the original TER game. -/
noncomputable def grundy : Finset (Vertex m) → ℕ := by
  classical
  exact (measure Finset.card).wf.fix fun R rec =>
    mex ((moves R).attach.image (fun Q => rec Q.1 (move_card_lt Q.2)))

theorem grundy_eq (R : Finset (Vertex m)) :
    grundy R = mex ((moves R).image grundy) := by
  classical
  rw [grundy, WellFounded.fix_eq]
  congr 1
  ext t
  simp only [mem_image, mem_attach]
  constructor
  · rintro ⟨Q, _, hQ⟩
    exact ⟨Q.1, Q.2, hQ⟩
  · rintro ⟨Q, hQ, ht⟩
    exact ⟨⟨Q, hQ⟩, trivial, ht⟩

private theorem grundy_zero_iff (R : Finset (Vertex m)) :
    grundy R = 0 ↔ ∀ Q ∈ moves R, grundy Q ≠ 0 := by
  classical
  obtain ⟨hmiss, hprev⟩ := mex_spec ((moves R).image grundy)
  rw [grundy_eq]
  constructor
  · intro h Q hQ hzero
    exact hmiss (mem_image.mpr ⟨Q, hQ, hzero.trans h.symm⟩)
  · intro h
    by_contra hn
    obtain ⟨Q, hQ, hzero⟩ := mem_image.mp (hprev 0 (Nat.pos_of_ne_zero hn))
    exact h Q hQ hzero

private theorem grundy_eq_zero_of_terminal {R : Finset (Vertex m)}
    (h : geoHull R ≠ Set.univ) : grundy R = 0 := by
  apply (grundy_zero_iff R).mpr
  intro Q hQ
  exact (h (mem_moves.mp hQ).1).elim

private theorem invariant_grundy_zero {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    {R : Finset (Vertex m)} (hR : Invariant k R) : grundy R = 0 := by
  induction k using Nat.strong_induction_on generalizing R with
  | h k ih =>
    apply (grundy_zero_iff R).mpr
    intro Q hQ
    obtain ⟨_, x, hx, rfl⟩ := mem_moves.mp hQ
    have hLive := first_erase_live hk hR x
    have hHull := (geoHull_eq_univ_iff _ hm).mpr hLive
    by_cases hbase : k = 2
    · have hfour : (R.erase x).card = 4 := by
        rw [card_erase_of_mem hx, hR.1, hbase]
      obtain ⟨y, hy, hterminal⟩ := four_terminal_reply hfour hLive
      have hmove : (R.erase x).erase y ∈ moves (R.erase x) :=
        mem_moves.mpr ⟨hHull, y, hy, rfl⟩
      have hzero := grundy_eq_zero_of_terminal
        (fun he => hterminal ((geoHull_eq_univ_iff _ hm).mp he))
      exact fun h => (grundy_zero_iff _).mp h _ hmove hzero
    · obtain ⟨y, hy, hnext⟩ := rank_reply hk hR hx
      have hmove : (R.erase x).erase y ∈ moves (R.erase x) :=
        mem_moves.mpr ⟨hHull, y, hy, rfl⟩
      have hzero := ih (k-1) (by omega) (by omega) hnext
      exact fun h => (grundy_zero_iff _).mp h _ hmove hzero

/-- The paper records the selected vertices. Complementing gives the survivor position. -/
noncomputable def terNim (selected : Finset (Vertex m)) : ℕ := grundy selectedᶜ

/-- Benesh–Ernst–Meyer–Salmon–Sieben, arXiv:2606.05483v1, Conjecture 5.5. -/
theorem conjecture_5_5 (m : ℕ) (hm : 2 ≤ m) :
    terNim (∅ : Finset (Vertex m)) = 0 := by
  simpa [terNim] using invariant_grundy_zero hm hm (initial_invariant m)

end OddCycleTER
