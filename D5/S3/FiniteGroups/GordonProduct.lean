/- GID: D5/S3/FiniteGroups/GordonProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GordonProduct
   mirror-E: none
   anchors: []
   utility: none
   digest: Gordon interleaving has distinct vertices and every nonzero directed difference. -/

import D5.S3.FiniteGroups.GordonCarry
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup

/-! Gordon's interleaved prefix path in an even cyclic factor and an odd digit box. -/

namespace D5.S3.FiniteGroups.Gordon

theorem volume_odd (ds : List OddRadix) : Odd (volume ds) := by
  induction ds with
  | nil => exact odd_one
  | cons d ds ih => exact d.odd.mul ih

private theorem box_card (ds : List OddRadix) : Fintype.card (Box ds) = volume ds := by
  exact (Fintype.card_congr (rankEquiv ds)).trans (Fintype.card_fin _)

private theorem residue_eq_iff (ds : List OddRadix) (u v : ℕ) :
    residue ds u = residue ds v ↔ u ≡ v [MOD volume ds] := by
  constructor
  · intro h
    simpa only [rank_residue, Nat.ModEq] using congrArg (rank ds) h
  · intro h
    apply (rankEquiv ds).injective
    apply Fin.ext
    change rank ds (residue ds u) = rank ds (residue ds v)
    simpa only [rank_residue, Nat.ModEq] using h

private theorem cast_rank_residue (ds : List OddRadix) (n : ℕ) :
    (rank ds (residue ds n) : ZMod (volume ds)) = n := by
  rw [rank_residue]
  simp

private theorem complement_congruence (ds : List OddRadix) (u v : ℕ)
    (he : -residue ds u = residue ds v + ones ds) :
    u + v + 1 ≡ 0 [MOD volume ds] := by
  have hv : residue ds v = -residue ds u - ones ds := by rw [he]; abel
  have hr := rank_complement ds (residue ds u)
  rw [← hv] at hr
  have hc := congrArg (fun n : ℕ => (n : ZMod (volume ds))) hr
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, cast_rank_residue,
    ZMod.natCast_self] using hc

/-- Coordinate map; the odd box is a set coding, not a homomorphic CRT. -/
def coordinate (h : ℕ) (ds : List OddRadix) (j : ℕ) : ZMod (2 * h) × Box ds :=
  (j, residue ds j)

/-- All N vertices, with the empty prefix at index zero. -/
def vertex (h : ℕ) (ds : List OddRadix) (k : ℕ) : ZMod (2 * h) × Box ds :=
  if k % 2 = 0 then -coordinate h ds (k / 2)
  else coordinate h ds (k / 2) + (1, ones ds)

private theorem vertex_even (h : ℕ) (ds : List OddRadix) (j : ℕ) :
    vertex h ds (2 * j) = -coordinate h ds j := by simp [vertex]

private theorem vertex_odd (h : ℕ) (ds : List OddRadix) (j : ℕ) :
    vertex h ds (2 * j + 1) = coordinate h ds j + (1, ones ds) := by
  have hj : (2 * j + 1) / 2 = j := by omega
  simp [vertex, hj]

private theorem vertex_zero (h : ℕ) (ds : List OddRadix) : vertex h ds 0 = 0 := by
  simp [vertex, coordinate, residue_zero]

private theorem coordinate_injective_bounded (h : ℕ) (ds : List OddRadix)
    (hc : (2 * h).Coprime (volume ds)) {u v : ℕ}
    (hu : u < 2 * (h * volume ds)) (hv : v < 2 * (h * volume ds))
    (he : coordinate h ds u = coordinate h ds v) : u = v := by
  have hq : u ≡ v [MOD 2 * h] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrArg Prod.fst he)
  have hd := (residue_eq_iff ds u v).mp (congrArg Prod.snd he)
  have ht := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨hq, hd⟩
  exact ht.eq_of_lt_of_lt (by simpa [Nat.mul_assoc] using hu)
    (by simpa [Nat.mul_assoc] using hv)

private theorem cross_vertex_ne (h : ℕ) (ds : List OddRadix)
    (hc : (2 * h).Coprime (volume ds)) {u v : ℕ}
    (hu : u < h * volume ds) (hv : v < h * volume ds) :
    -coordinate h ds u ≠ coordinate h ds v + (1, ones ds) := by
  intro he
  have hfirst := congrArg Prod.fst he
  change -(u : ZMod (2 * h)) = (v : ZMod (2 * h)) + 1 at hfirst
  have hq : u + v + 1 ≡ 0 [MOD 2 * h] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    linear_combination -hfirst
  have hd := complement_congruence ds u v (congrArg Prod.snd he)
  have ht := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨hq, hd⟩
  have hz := ht.eq_of_lt_of_lt (by nlinarith : u + v + 1 < (2 * h) * volume ds)
    (by have := volume_pos ds; nlinarith : 0 < (2 * h) * volume ds)
  omega

/-- Same-parity CRT and opposite-parity digit complement separate every prefix. -/
theorem vertex_injective (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) :
    Function.Injective (fun k : Fin (2 * (h * volume ds)) => vertex h ds k.val) := by
  have hq : (2 * h).Coprime (volume ds) :=
    (Nat.coprime_two_left.mpr (volume_odd ds)).mul_left hc
  intro k l he
  have hk := k.isLt
  have hl := l.isLt
  have hkmod := Nat.mod_lt k.val (by decide : 0 < 2)
  have hlmod := Nat.mod_lt l.val (by decide : 0 < 2)
  by_cases hke : k.val % 2 = 0 <;> by_cases hle : l.val % 2 = 0
  · have hh : coordinate h ds (k.val / 2) = coordinate h ds (l.val / 2) := by
      simpa only [vertex, hke, hle, ite_true, neg_inj] using he
    have hi := coordinate_injective_bounded h ds hq (u := k.val / 2) (v := l.val / 2)
      (by omega) (by omega) hh
    apply Fin.ext
    omega
  · have hh : -coordinate h ds (k.val / 2) =
        coordinate h ds (l.val / 2) + (1, ones ds) := by
      simpa only [vertex, hke, hle, ite_true, ite_false] using he
    exact (cross_vertex_ne h ds hq (by omega) (by omega) hh).elim
  · have hh : -coordinate h ds (l.val / 2) =
        coordinate h ds (k.val / 2) + (1, ones ds) := by
      simpa only [vertex, hke, hle, ite_true, ite_false] using he.symm
    exact (cross_vertex_ne h ds hq (by omega) (by omega) hh).elim
  · have hh : coordinate h ds (k.val / 2) = coordinate h ds (l.val / 2) := by
      apply add_right_cancel
      simpa only [vertex, hke, hle, ite_false] using he
    have hi := coordinate_injective_bounded h ds hq (u := k.val / 2) (v := l.val / 2)
      (by omega) (by omega) hh
    apply Fin.ext
    omega

/-- Odd-first-coordinate differences, including the initial edge. -/
def oddLabel (h : ℕ) (ds : List OddRadix) (j : ℕ) : ZMod (2 * h) × Box ds :=
  ((2 * j + 1 : ℕ), residue ds j + residue ds j + ones ds)

/-- Even-first-coordinate differences; index zero gives the omitted zero label. -/
def evenLabel (h : ℕ) (ds : List OddRadix) (j : ℕ) : ZMod (2 * h) × Box ds :=
  (-((2 * j : ℕ) : ZMod (2 * h)), carry ds (residue ds j))

private theorem odd_difference (h : ℕ) (ds : List OddRadix) (j : ℕ) :
    vertex h ds (2 * j + 1) - vertex h ds (2 * j) = oddLabel h ds j := by
  rw [vertex_odd, vertex_even]
  apply Prod.ext
  · simp [coordinate, oddLabel]
    ring
  · change (residue ds j + ones ds) - -residue ds j = _
    dsimp [oddLabel]
    abel

private theorem even_difference (h : ℕ) (ds : List OddRadix) (j : ℕ) (hj : 0 < j) :
    vertex h ds (2 * j) - vertex h ds (2 * j - 1) = evenLabel h ds j := by
  have hi : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
  rw [hi, vertex_even, vertex_odd]
  apply Prod.ext
  · change -(j : ZMod (2 * h)) - (((j - 1 : ℕ) : ZMod (2 * h)) + 1) = _
    dsimp [evenLabel]
    have hn : (((j - 1 : ℕ) : ZMod (2 * h)) + 1) = (j : ZMod (2 * h)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun z : ℕ => (z : ZMod (2 * h))) (Nat.sub_add_cancel hj)
    rw [hn]
    push_cast
    ring
  · change -residue ds j - (residue ds (j - 1) + ones ds) = carry ds (residue ds j)
    rw [carry, pred_residue ds j hj]
    abel

private theorem half_congruence (h u v : ℕ)
    (he : ((2 * u : ℕ) : ZMod (2 * h)) = ((2 * v : ℕ) : ZMod (2 * h))) :
    u ≡ v [MOD h] :=
  Nat.ModEq.mul_left_cancel' (by decide : 2 ≠ 0)
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp he)

private theorem odd_label_injective (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) {u v : ℕ}
    (hu : u < h * volume ds) (hv : v < h * volume ds)
    (he : oddLabel h ds u = oddLabel h ds v) : u = v := by
  have hfirst := congrArg Prod.fst he
  change ((2 * u + 1 : ℕ) : ZMod (2 * h)) = ((2 * v + 1 : ℕ) : ZMod (2 * h)) at hfirst
  have hq : u ≡ v [MOD h] := half_congruence h u v (by
    push_cast at hfirst ⊢
    exact add_right_cancel hfirst)
  have hsecond := congrArg Prod.snd he
  change residue ds u + residue ds u + ones ds =
    residue ds v + residue ds v + ones ds at hsecond
  have hd := (residue_eq_iff ds u v).mp (box_two_injective ds (add_right_cancel hsecond))
  exact ((Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨hq, hd⟩).eq_of_lt_of_lt hu hv

private theorem even_label_injective (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) {u v : ℕ}
    (hu : u < h * volume ds) (hv : v < h * volume ds)
    (he : evenLabel h ds u = evenLabel h ds v) : u = v := by
  have hfirst := congrArg Prod.fst he
  change -((2 * u : ℕ) : ZMod (2 * h)) = -((2 * v : ℕ) : ZMod (2 * h)) at hfirst
  have hq := half_congruence h u v (neg_injective hfirst)
  have hd := (residue_eq_iff ds u v).mp (carry_injective ds (congrArg Prod.snd he))
  exact ((Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨hq, hd⟩).eq_of_lt_of_lt hu hv

private theorem labels_disjoint (h : ℕ) (ds : List OddRadix) (u v : ℕ) :
    oddLabel h ds u ≠ evenLabel h ds v := by
  intro he
  have hfirst := congrArg Prod.fst he
  change ((2 * u + 1 : ℕ) : ZMod (2 * h)) = -((2 * v : ℕ) : ZMod (2 * h)) at hfirst
  have hz : ((2 * u + 1 + 2 * v : ℕ) : ZMod (2 * h)) = 0 := by
    push_cast at hfirst ⊢
    linear_combination hfirst
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have htwo : 2 ∣ 2 * u + 1 + 2 * v := dvd_trans (dvd_mul_right 2 h) hd
  omega

private theorem even_label_zero (h : ℕ) (ds : List OddRadix) : evenLabel h ds 0 = 0 := by
  apply Prod.ext
  · simp [evenLabel]
  · exact (carry_eq_zero ds (residue ds 0)).mpr (residue_zero ds)

private theorem even_label_ne_zero (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) {j : ℕ} (hj : 0 < j) (hjl : j < h * volume ds) :
    evenLabel h ds j ≠ 0 := by
  intro he
  have hzero := (carry_eq_zero ds (residue ds j)).mp (congrArg Prod.snd he)
  have hd : j ≡ 0 [MOD volume ds] :=
    (residue_eq_iff ds j 0).mp (hzero.trans (residue_zero ds).symm)
  have hq : j ≡ 0 [MOD h] := half_congruence h j 0 (by
    have hf := congrArg Prod.fst he
    change -((2 * j : ℕ) : ZMod (2 * h)) = 0 at hf
    simpa using neg_eq_zero.mp hf)
  have hz := ((Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨hq, hd⟩).eq_of_lt_of_lt hjl
    (by omega : 0 < h * volume ds)
  omega

/-- Every successive directed difference in the N-vertex path. -/
def difference (h : ℕ) (ds : List OddRadix) (t : ℕ) : ZMod (2 * h) × Box ds :=
  vertex h ds (t + 1) - vertex h ds t

private theorem difference_even (h : ℕ) (ds : List OddRadix) (j : ℕ) :
    difference h ds (2 * j) = oddLabel h ds j := odd_difference h ds j

private theorem difference_odd (h : ℕ) (ds : List OddRadix) (j : ℕ) :
    difference h ds (2 * j + 1) = evenLabel h ds (j + 1) := by
  have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  have hprev : 2 * j + 1 = 2 * (j + 1) - 1 := by omega
  unfold difference
  rw [hnext, hprev]
  exact even_difference h ds (j + 1) (by omega)

/-- Carry inversion proves even-label uniqueness; parity separates the two inventories. -/
theorem difference_injective (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) :
    Function.Injective (fun t : Fin (2 * (h * volume ds) - 1) => difference h ds t.val) := by
  intro t s he
  change difference h ds t.val = difference h ds s.val at he
  have ht := t.isLt
  have hs := s.isLt
  have htt := Nat.mod_add_div t.val 2
  have hss := Nat.mod_add_div s.val 2
  have htm := Nat.mod_lt t.val (by decide : 0 < 2)
  have hsm := Nat.mod_lt s.val (by decide : 0 < 2)
  by_cases hte : t.val % 2 = 0 <;> by_cases hse : s.val % 2 = 0
  · have hti : t.val = 2 * (t.val / 2) := by omega
    have hsi : s.val = 2 * (s.val / 2) := by omega
    rw [hti, hsi, difference_even, difference_even] at he
    have hi := odd_label_injective h ds hc (by omega) (by omega) he
    apply Fin.ext; omega
  · have hti : t.val = 2 * (t.val / 2) := by omega
    have hsi : s.val = 2 * (s.val / 2) + 1 := by omega
    rw [hti, hsi, difference_even, difference_odd] at he
    exact (labels_disjoint h ds _ _ he).elim
  · have hti : t.val = 2 * (t.val / 2) + 1 := by omega
    have hsi : s.val = 2 * (s.val / 2) := by omega
    rw [hti, hsi, difference_odd, difference_even] at he
    exact (labels_disjoint h ds _ _ he.symm).elim
  · have hti : t.val = 2 * (t.val / 2) + 1 := by omega
    have hsi : s.val = 2 * (s.val / 2) + 1 := by omega
    rw [hti, hsi, difference_odd, difference_odd] at he
    have hi := even_label_injective h ds hc (by omega) (by omega) he
    apply Fin.ext; omega

private theorem difference_ne_zero (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) (t : Fin (2 * (h * volume ds) - 1)) :
    difference h ds t.val ≠ 0 := by
  have ht := t.isLt
  have htt := Nat.mod_add_div t.val 2
  have htm := Nat.mod_lt t.val (by decide : 0 < 2)
  by_cases hte : t.val % 2 = 0
  · have hti : t.val = 2 * (t.val / 2) := by omega
    rw [hti, difference_even, ← even_label_zero h ds]
    exact labels_disjoint h ds _ _
  · have hti : t.val = 2 * (t.val / 2) + 1 := by omega
    rw [hti, difference_odd]
    exact even_label_ne_zero h ds hc (by omega) (by omega)

/-- The original directed labels of the Gordon path, each with coefficient one. -/
def word (h : ℕ) (ds : List OddRadix) : List (ZMod (2 * h) × Box ds) :=
  (List.range (2 * (h * volume ds) - 1)).map (difference h ds)

/-- Telescoping includes the empty prefix and the complete word. -/
theorem word_prefix (h : ℕ) (ds : List OddRadix) (k : ℕ)
    (hk : k ≤ (word h ds).length) : (List.take k (word h ds)).sum = vertex h ds k := by
  have hk' : k ≤ 2 * (h * volume ds) - 1 := by simpa [word] using hk
  unfold word
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk']
  change ((List.range k).map (fun j => vertex h ds (j + 1) - vertex h ds j)).sum = _
  rw [List.sum_range_sub, vertex_zero, sub_zero]

private theorem word_nodup (h : ℕ) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) : (word h ds).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_range)
  intro u hu v hv he
  have hu' := List.mem_range.mp hu
  have hv' := List.mem_range.mp hv
  exact congrArg Fin.val (difference_injective h ds hc (a₁ := ⟨u, hu'⟩) (a₂ := ⟨v, hv'⟩) he)

/-- The label inventory is the entire nonzero group, with no cyclicity assumption on the odd box. -/
theorem word_mem_iff (h : ℕ) (hh : 0 < h) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) (x : ZMod (2 * h) × Box ds) :
    x ∈ word h ds ↔ x ≠ 0 := by
  classical
  letI : NeZero (2 * h) := ⟨by omega⟩
  let f : Fin (2 * (h * volume ds) - 1) → {x : ZMod (2 * h) × Box ds // x ≠ 0} :=
    fun t => ⟨difference h ds t.val, difference_ne_zero h ds hc t⟩
  have hcard : Fintype.card {x : ZMod (2 * h) × Box ds // x ≠ 0} =
      2 * (h * volume ds) - 1 := by
    rw [Fintype.card_subtype_compl (fun x : ZMod (2 * h) × Box ds => x = 0),
      Fintype.card_subtype_eq, Fintype.card_prod, ZMod.card, box_card]
    simp only [Nat.mul_assoc]
  have hbij : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
    constructor
    · intro u v he
      exact difference_injective h ds hc (congrArg Subtype.val he)
    · simpa only [Fintype.card_fin] using hcard.symm
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact difference_ne_zero h ds hc ⟨j, List.mem_range.mp hj⟩
  · intro hx
    obtain ⟨j, hj⟩ := hbij.surjective ⟨x, hx⟩
    exact List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, congrArg Subtype.val hj⟩

/-- Full-set sequencing records all prefixes, including indices zero and length. -/
def FullSequencing {G : Type*} [AddCommGroup G] (w : List G) : Prop :=
  w.Nodup ∧ (∀ x : G, x ∈ w ↔ x ≠ 0) ∧
    Function.Injective (fun k : Fin (w.length + 1) => (w.take k.val).sum)

/-- Complete product theorem, including q=2, no odd factors, and repeated odd radices. -/
theorem product_sequencing (h : ℕ) (hh : 0 < h) (ds : List OddRadix)
    (hc : h.Coprime (volume ds)) : FullSequencing (word h ds) := by
  refine ⟨word_nodup h ds hc, word_mem_iff h hh ds hc, ?_⟩
  intro k l he
  change ((word h ds).take k.val).sum = ((word h ds).take l.val).sum at he
  have hk : k.val ≤ (word h ds).length := by omega
  have hl : l.val ≤ (word h ds).length := by omega
  rw [word_prefix h ds _ hk, word_prefix h ds _ hl] at he
  have hvol := volume_pos ds
  have hL : 0 < h * volume ds := Nat.mul_pos hh hvol
  have hlen : (word h ds).length + 1 = 2 * (h * volume ds) := by simp [word]; omega
  have hh' := vertex_injective h ds hc (a₁ := ⟨k.val, by omega⟩) (a₂ := ⟨l.val, by omega⟩) he
  apply Fin.ext
  exact congrArg (fun z : Fin (2 * (h * volume ds)) => z.val) hh'

/-- The full prefix is the distinguished involution of the even cyclic coordinate. -/
theorem word_endpoint (h : ℕ) (hh : 0 < h) (ds : List OddRadix) :
    (word h ds).sum = ((h : ZMod (2 * h)), (0 : Box ds)) := by
  have hL : 0 < h * volume ds := Nat.mul_pos hh (volume_pos ds)
  have hr : residue ds (h * volume ds) = 0 := by
    rw [← residue_zero ds, residue_eq_iff]
    simp [Nat.ModEq]
  have hp := pred_residue ds (h * volume ds) hL
  rw [hr] at hp
  have hz : pred ds 0 = -ones ds := by
    have hc := (carry_eq_zero ds 0).mpr rfl
    have he : -pred ds 0 - ones ds = 0 := by simpa [carry] using hc
    exact neg_eq_iff_eq_neg.mp (sub_eq_zero.mp he)
  have hb : residue ds (h * volume ds - 1) = -ones ds := hp.symm.trans hz
  have hsum := word_prefix h ds (word h ds).length le_rfl
  simp only [List.take_length] at hsum
  rw [hsum]
  have hlen : (word h ds).length = 2 * (h * volume ds - 1) + 1 := by simp [word]; omega
  rw [hlen, vertex_odd]
  apply Prod.ext
  · change ((h * volume ds - 1 : ℕ) : ZMod (2 * h)) + 1 = (h : ZMod (2 * h))
    have hn : ((h * volume ds - 1 : ℕ) : ZMod (2 * h)) + 1 =
        ((h * volume ds : ℕ) : ZMod (2 * h)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun z : ℕ => (z : ZMod (2 * h))) (Nat.sub_add_cancel hL)
    rw [hn]
    obtain ⟨k, hk⟩ := volume_odd ds
    have he : h * volume ds = h + (2 * h) * k := by rw [hk]; ring
    rw [he]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  · change residue ds (h * volume ds - 1) + ones ds = 0
    rw [hb, neg_add_cancel]

end D5.S3.FiniteGroups.Gordon
