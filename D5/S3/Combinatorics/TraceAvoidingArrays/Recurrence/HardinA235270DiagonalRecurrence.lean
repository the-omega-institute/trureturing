/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The eleven-lag recurrence for Hardin's constant-stress squares. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
import Batteries.Tactic.OpenPrivate

/-! Complementary row-fiber counts give the dependence on both dimensions of the square. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open Polynomial hiding C
open scoped BigOperators
open private Sequence shift_pow_apply Kills kills_of_dvd kills_zero kills_sum kills_smul
  eval_C_mul_X_pow kills_step linear quadratic from D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
open private Row Profile edge Fiber flip profileAt b profileCount fiber_bound literal_sum from
  D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence

noncomputable section

private abbrev OddIndex (k : ℕ) := {i : Fin (k + 2) // i.val % 2 ≠ 0}

private instance (k : ℕ) : Nonempty (OddIndex k) :=
  ⟨⟨⟨1, by omega⟩, by change 1 % 2 ≠ 0; decide⟩⟩

private def rank {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : OddIndex k => (r.1 i.1).val)

private theorem rank_le {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p)
    (i : Fin (k + 2)) (hi : i.val % 2 ≠ 0) : rank r ≤ (r.1 i).val :=
  Finset.inf'_le _ (Finset.mem_univ (⟨i, hi⟩ : OddIndex k))

private theorem rank_attained {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p) :
    ∃ i : OddIndex k, rank r = (r.1 i.1).val := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : OddIndex k => (r.1 i.1).val)
  exact ⟨i, hi⟩

private theorem fiber_difference {d k : ℕ} {p : Profile d k} (r s : Fiber p)
    (i : Fin (k + 1)) :
    ((r.1 i).val : ℤ) - (s.1 i).val =
      if i.val % 2 = 0 then ((r.1 0).val : ℤ) - (s.1 0).val
      else ((s.1 0).val : ℤ) - (r.1 0).val := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hr := r.2 i
    have hs := s.2 i
    simp only [edge] at hr hs
    simp only [Fin.val_castSucc, Fin.val_succ] at ih ⊢
    by_cases hi : i.val % 2 = 0
    · have hn : (i.val + 1) % 2 ≠ 0 := by omega
      simp only [hi, hn, ite_true, ite_false] at ih ⊢
      omega
    · have hn : (i.val + 1) % 2 = 0 := by omega
      simp only [hi, hn, ite_true, ite_false] at ih ⊢
      omega

private theorem rank_injective {d k : ℕ} (p : Profile d (k + 1)) :
    Function.Injective (rank (p := p)) := by
  intro r s h
  obtain ⟨i, hi⟩ := rank_attained r
  obtain ⟨j, hj⟩ := rank_attained s
  have di := fiber_difference r s i.1
  have dj := fiber_difference r s j.1
  simp only [i.2, j.2, ite_false] at di dj
  have li := rank_le s i.1 i.2
  have lj := rank_le r j.1 j.2
  have h0 : (r.1 0).val = (s.1 0).val := by omega
  apply Subtype.ext
  funext t
  apply Fin.ext
  have dt := fiber_difference r s t
  rw [h0, sub_self, ite_self] at dt
  omega

private theorem even_room {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p)
    (i : Fin (k + 2)) (hi : i.val % 2 = 0) :
    (r.1 i).val + rank r ≤ d := by
  by_cases hz : i.val = 0
  · let j : Fin (k + 1) := 0
    have e : j.castSucc = i := Fin.ext hz.symm
    have hm := rank_le r j.succ (by change 1 % 2 ≠ 0; decide)
    have he := r.2 j
    have hb := (p j).isLt
    rw [edge, e] at he
    omega
  · let j : Fin (k + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
    have e : j.succ = i := Fin.ext (by dsimp [j]; omega)
    have hm := rank_le r j.castSucc (by dsimp [j]; omega)
    have he := r.2 j
    have hb := (p j).isLt
    rw [edge, e] at he
    omega

private def slide {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p) (t : ℕ)
    (ht : t ≤ rank r) : Fiber p :=
  ⟨fun i => if hi : i.val % 2 = 0 then
      ⟨(r.1 i).val + t, by have := even_room r i hi; omega⟩
    else ⟨(r.1 i).val - t, lt_of_le_of_lt (Nat.sub_le ..) (r.1 i).isLt⟩,
    fun j => by
      have he := r.2 j
      simp only [edge, Fin.val_castSucc, Fin.val_succ] at he ⊢
      by_cases hj : j.val % 2 = 0
      · have hs : (j.val + 1) % 2 ≠ 0 := by omega
        have hm := rank_le r j.succ hs
        simp only [hj, hs, dite_true, dite_false]
        omega
      · have hs : (j.val + 1) % 2 = 0 := by omega
        have hm := rank_le r j.castSucc hj
        simp only [hj, hs, dite_true, dite_false]
        omega⟩

private theorem rank_slide {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p) (t : ℕ)
    (ht : t ≤ rank r) : rank (slide r t ht) = rank r - t := by
  obtain ⟨i, hi⟩ := rank_attained r
  obtain ⟨j, hj⟩ := rank_attained (slide r t ht)
  have h₁ := rank_le (slide r t ht) i.1 i.2
  have h₂ := rank_le r j.1 j.2
  have evalOdd (i : OddIndex k) : ((slide r t ht).1 i.1).val = (r.1 i.1).val - t := by
    have hOdd := i.2
    simp only [slide, hOdd, dite_false]
  rw [evalOdd i] at h₁
  rw [evalOdd j] at hj
  omega

private def Anchor {d k : ℕ} (p : Profile d (k + 1)) (t : ℕ) :=
  {r : Fiber p // t ≤ rank r}

private instance {d k : ℕ} (p : Profile d (k + 1)) (t : ℕ) : Finite (Anchor p t) := by
  unfold Anchor
  infer_instance

private theorem anchor_iff {d k : ℕ} {p : Profile d (k + 1)} (r : Fiber p) (t : ℕ) :
    t ≤ rank r ↔ ∀ i : OddIndex k, t ≤ (r.1 i.1).val := by
  constructor
  · exact fun h i => h.trans (rank_le r i.1 i.2)
  · intro h
    obtain ⟨i, hi⟩ := rank_attained r
    rw [hi]
    exact h i

private theorem rank_range {d k : ℕ} (p : Profile d (k + 1)) (u : ℕ) :
    (∃ r : Fiber p, rank r = u) ↔ u < b p := by
  classical
  let := Fintype.ofFinite (Fiber p)
  let s := Finset.univ.image (rank (p := p))
  have mem (v : ℕ) : v ∈ s ↔ ∃ r : Fiber p, rank r = v := by
    simp [s]
  have card : s.card = b p := by
    rw [b, Nat.card_eq_fintype_card]
    exact Finset.card_image_of_injective _ (rank_injective p)
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := s.max'_mem hs
    obtain ⟨r, hr⟩ := (mem m).mp hm
    have eqRange : s = Finset.range (m + 1) := by
      ext v
      rw [Finset.mem_range]
      constructor
      · intro hv
        exact Nat.lt_succ_of_le (s.le_max' v hv)
      · intro hv
        have h : m - v ≤ rank r := by omega
        exact (mem v).mpr ⟨slide r (m - v) h, by rw [rank_slide]; omega⟩
    have e : b p = m + 1 := by rw [← card, eqRange, Finset.card_range]
    rw [← mem, eqRange, e, Finset.mem_range]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [← mem, ← card, he]
    simp

private theorem card_anchor {d k : ℕ} (p : Profile d (k + 1)) (t : ℕ) :
    Nat.card (Anchor p t) = b p - t := by
  let f (r : Anchor p t) : Fin (b p - t) :=
    ⟨rank r.1 - t, by
      have h := (rank_range p (rank r.1)).mp ⟨r.1, rfl⟩
      have ht := r.2
      omega⟩
  have hi : Function.Injective f := by
    intro r s e
    have he := congrArg Fin.val e
    change rank r.1 - t = rank s.1 - t at he
    have hr := r.2
    have hs := s.2
    exact Subtype.ext (rank_injective p (by omega))
  have hs : Function.Surjective f := by
    intro j
    have hj := j.isLt
    obtain ⟨r, hr⟩ := (rank_range p (j.val + t)).mpr (by omega)
    exact ⟨⟨r, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩), Nat.card_fin]

private theorem flip_edge {d k : ℕ} (p : Profile d k) (j : Fin k) :
    (p j).val + (flip p j).val = d := by
  have := (p j).isLt
  change (p j).val + (p j).rev.val = d
  simp only [Fin.val_rev]
  omega

private def parityTotal (d q i : ℕ) : ℕ := if i % 2 = 0 then q else d - q

private theorem parityTotal_add_adj (d q i : ℕ) (hq : q ≤ d) :
    parityTotal d q i + parityTotal d q (i + 1) = d := by
  by_cases hi : i % 2 = 0
  · have hn : (i + 1) % 2 ≠ 0 := by omega
    simp only [parityTotal, hi, hn, ite_true, ite_false]
    omega
  · have hn : (i + 1) % 2 = 0 := by omega
    simp only [parityTotal, hi, hn, ite_true, ite_false]
    omega

private theorem anchorPair_sum {d k : ℕ} {p : Profile d (k + 1)}
    (r : Fiber p) (s : Fiber (flip p)) (i : Fin (k + 2)) :
    (r.1 i).val + (s.1 i).val = parityTotal d ((r.1 0).val + (s.1 0).val) i.val := by
  have firstBound : (r.1 0).val + (s.1 0).val ≤ d := by
    have he := flip_edge p 0
    rw [← r.2 0, ← s.2 0] at he
    simp only [edge] at he
    have hz : (0 : Fin (k + 1)).castSucc = 0 := rfl
    rw [hz] at he
    omega
  induction i using Fin.induction with
  | zero => simp [parityTotal]
  | succ j ih =>
    have he := flip_edge p j
    rw [← r.2 j, ← s.2 j] at he
    simp only [edge] at he
    have hh := parityTotal_add_adj d ((r.1 0).val + (s.1 0).val) j.val firstBound
    simp only [Fin.val_castSucc, Fin.val_succ] at ih ⊢
    omega

private theorem anchorPair_firstBound {d k : ℕ} {p : Profile d (k + 1)}
    (r : Fiber p) (s : Fiber (flip p)) : (r.1 0).val + (s.1 0).val ≤ d := by
  have he := flip_edge p 0
  rw [← r.2 0, ← s.2 0] at he
  simp only [edge] at he
  have hz : (0 : Fin (k + 1)).castSucc = 0 := rfl
  rw [hz] at he
  omega

private def oddLower (a i : ℕ) : ℕ := if i % 2 = 0 then 0 else a

private def columnSlots (d q a t i : ℕ) : ℕ :=
  parityTotal d q i + 1 - (oddLower a i + oddLower t i)

private abbrev AnchorPairs (d k a t : ℕ) :=
  Σ p : Profile d (k + 1), Anchor p a × Anchor (flip p) t

private abbrev ColumnChoices (d k a t : ℕ) :=
  Σ q : Fin (d + 1), (i : Fin (k + 2)) → Fin (columnSlots d q.val a t i.val)

private theorem anchor_lower {d k : ℕ} {p : Profile d (k + 1)} {a : ℕ}
    (r : Anchor p a) (i : Fin (k + 2)) : oddLower a i.val ≤ (r.1.1 i).val := by
  by_cases hi : i.val % 2 = 0
  · simp [oddLower, hi]
  · simpa [oddLower, hi] using (anchor_iff r.1 a).mp r.2 ⟨i, hi⟩

private def toColumns {d k a t : ℕ} (z : AnchorPairs d k a t) : ColumnChoices d k a t :=
  let r := z.2.1.1
  let s := z.2.2.1
  let q : Fin (d + 1) := ⟨(r.1 0).val + (s.1 0).val, Nat.lt_succ_of_le (anchorPair_firstBound r s)⟩
  ⟨q, fun i => ⟨(r.1 i).val - oddLower a i.val, by
    have hr := anchor_lower z.2.1 i
    have hs := anchor_lower z.2.2 i
    have he := anchorPair_sum r s i
    change (r.1 i).val - oddLower a i.val < columnSlots d q.val a t i.val
    dsimp only [columnSlots, q]
    change oddLower a i.val ≤ (r.1 i).val at hr
    change oddLower t i.val ≤ (s.1 i).val at hs
    omega⟩⟩

private def leftCell {d k a t : ℕ} (z : ColumnChoices d k a t) (i : Fin (k + 2)) : ℕ :=
  oddLower a i.val + (z.2 i).val

private def rightCell {d k a t : ℕ} (z : ColumnChoices d k a t) (i : Fin (k + 2)) : ℕ :=
  parityTotal d z.1.val i.val - leftCell z i

private theorem leftCell_bound {d k a t : ℕ} (z : ColumnChoices d k a t) (i : Fin (k + 2)) :
    leftCell z i + oddLower t i.val ≤ parityTotal d z.1.val i.val := by
  have h := (z.2 i).isLt
  dsimp only [columnSlots] at h
  unfold leftCell
  omega

private theorem cells_sum {d k a t : ℕ} (z : ColumnChoices d k a t) (i : Fin (k + 2)) :
    leftCell z i + rightCell z i = parityTotal d z.1.val i.val := by
  have h := leftCell_bound z i
  unfold rightCell
  omega

private theorem parityTotal_le {d q i : ℕ} (h : q ≤ d) : parityTotal d q i ≤ d := by
  unfold parityTotal
  split <;> omega

private def fromColumns {d k a t : ℕ} (z : ColumnChoices d k a t) : AnchorPairs d k a t := by
  have hq : z.1.val ≤ d := Nat.le_of_lt_succ z.1.isLt
  let r : Row d (k + 1) := fun i => ⟨leftCell z i, by
    have h := cells_sum z i
    have hb := parityTotal_le (i := i.val) hq
    omega⟩
  let s : Row d (k + 1) := fun i => ⟨rightCell z i, by
    have h := cells_sum z i
    have hb := parityTotal_le (i := i.val) hq
    omega⟩
  have hEdges (j : Fin (k + 1)) : edge r j + edge s j = d := by
    have e₁ := cells_sum z j.castSucc
    have e₂ := cells_sum z j.succ
    have h := parityTotal_add_adj d z.1.val j.val hq
    simp only [Fin.val_castSucc, Fin.val_succ] at e₁ e₂
    dsimp [edge, r, s]
    omega
  let p : Profile d (k + 1) := fun j => ⟨edge r j, by have := hEdges j; omega⟩
  let rf : Fiber p := ⟨r, fun _ => rfl⟩
  let sf : Fiber (flip p) := ⟨s, fun j => by
    have h := flip_edge p j
    change edge r j + (flip p j).val = d at h
    have e := hEdges j
    omega⟩
  exact ⟨p, ⟨rf, (anchor_iff rf a).mpr fun i => by
    change a ≤ leftCell z i.1
    simp [leftCell, oddLower, i.2]⟩,
    ⟨sf, (anchor_iff sf t).mpr fun i => by
      change t ≤ rightCell z i.1
      have h := leftCell_bound z i.1
      rw [show oddLower t i.1.val = t by simp [oddLower, i.2]] at h
      unfold rightCell
      omega⟩⟩

private theorem anchorPairs_ext {d k a t : ℕ} (z w : AnchorPairs d k a t)
    (hr : ∀ i, (z.2.1.1.1 i).val = (w.2.1.1.1 i).val)
    (hs : ∀ i, (z.2.2.1.1 i).val = (w.2.2.1.1 i).val) : z = w := by
  have hrow : z.2.1.1.1 = w.2.1.1.1 := funext fun i => Fin.ext (hr i)
  have hp : z.1 = w.1 := by
    funext j
    apply Fin.ext
    rw [← z.2.1.1.2 j, ← w.2.1.1.2 j, hrow]
  obtain ⟨p, r, s⟩ := z
  obtain ⟨q, u, v⟩ := w
  dsimp only at hp
  subst q
  have h₁ : r = u := Subtype.ext (Subtype.ext hrow)
  have h₂ : s = v := Subtype.ext (Subtype.ext (funext fun i => Fin.ext (hs i)))
  subst u
  subst v
  rfl

private theorem columnChoices_ext {d k a t : ℕ} (z w : ColumnChoices d k a t)
    (hq : z.1.val = w.1.val) (hc : ∀ i, (z.2 i).val = (w.2 i).val) : z = w := by
  have he : z.1 = w.1 := Fin.ext hq
  obtain ⟨q, f⟩ := z
  obtain ⟨u, g⟩ := w
  dsimp only at he
  subst u
  have e : f = g := funext fun i => Fin.ext (hc i)
  subst g
  rfl

private def anchorPairEquiv (d k a t : ℕ) :
    AnchorPairs d k a t ≃ ColumnChoices d k a t where
  toFun := toColumns
  invFun := fromColumns
  left_inv z := by
    apply anchorPairs_ext
    · intro i
      change leftCell (toColumns z) i = _
      have h := anchor_lower z.2.1 i
      change oddLower a i.val + ((z.2.1.1.1 i).val - oddLower a i.val) = _
      omega
    · intro i
      change rightCell (toColumns z) i = _
      have h := anchor_lower z.2.1 i
      have e := anchorPair_sum z.2.1.1 z.2.2.1 i
      change parityTotal d ((z.2.1.1.1 0).val + (z.2.2.1.1 0).val) i.val -
        (oddLower a i.val + ((z.2.1.1.1 i).val - oddLower a i.val)) = _
      omega
  right_inv z := by
    apply columnChoices_ext
    · change leftCell z 0 + rightCell z 0 = z.1.val
      simpa [parityTotal] using cells_sum z (0 : Fin (k + 2))
    · intro i
      change (oddLower a i.val + (z.2 i).val) - oddLower a i.val = (z.2 i).val
      omega

private def alternatingWeight {R : Type*} [CommMonoid R] (a t : R) (h : ℕ) : R :=
  a ^ ((h + 1) / 2) * t ^ (h / 2)

private theorem alternatingWeight_step {R : Type*} [CommMonoid R] (a t : R) (h : ℕ) :
    alternatingWeight a t (h + 2) = (a * t) * alternatingWeight a t h := by
  have e : (h + 2 + 1) / 2 = (h + 1) / 2 + 1 := by omega
  have o : (h + 2) / 2 = h / 2 + 1 := by omega
  simp only [alternatingWeight, e, o, pow_succ]
  ac_rfl

private theorem parity_product {R : Type*} [CommMonoid R] (a t : R) (h : ℕ) :
    (∏ i : Fin h, if i.val % 2 = 0 then a else t) = alternatingWeight a t h := by
  induction h using Nat.twoStepInduction with
  | zero => simp [alternatingWeight]
  | one => simp [alternatingWeight]
  | more h ih _ =>
    rw [alternatingWeight_step, ← ih, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.zero_mod, ite_true]
    have shiftParity (i : Fin h) : (i.val + 1 + 1) % 2 = i.val % 2 := by omega
    simp only [Nat.zero_add, Nat.mod_succ, shiftParity, mul_assoc, Nat.one_ne_zero, ite_false]

private theorem profileCount_weight {d k : ℕ} (p : Profile d k) (h : ℕ) :
    profileCount p h = alternatingWeight (b p) (b (flip p)) h := by
  rw [← parity_product]
  unfold profileCount
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i.val % 2 = 0 <;> simp [profileAt, hi]

private theorem natCast_weight (a t h : ℕ) :
    ((alternatingWeight a t h : ℕ) : ℤ) = alternatingWeight (a : ℤ) (t : ℤ) h := by
  simp [alternatingWeight]

private theorem columnSlots_parity (d q a t i : ℕ) :
    columnSlots d q a t i = if i % 2 = 0 then q + 1 else d - q + 1 - (a + t) := by
  by_cases hi : i % 2 = 0 <;> simp [columnSlots, parityTotal, oddLower, hi]

private theorem anchorMoment_nat (d k a t : ℕ) :
    (∑ p : Profile d (k + 1), (b p - a) * (b (flip p) - t)) =
      ∑ q : Fin (d + 1), alternatingWeight (q.val + 1) (d - q.val + 1 - (a + t)) (k + 2) := by
  have h := Nat.card_congr (anchorPairEquiv d k a t)
  simp only [Nat.card_sigma, Nat.card_prod, card_anchor, Nat.card_pi, Nat.card_fin,
    columnSlots_parity, parity_product] at h
  exact h

private def anchorMoment (k a t : ℕ) : ℤ :=
  ∑ p : Profile 3 (k + 1), ((b p - a : ℕ) : ℤ) * ((b (flip p) - t : ℕ) : ℤ)

private theorem anchorMoment_formula (k a t : ℕ) :
    anchorMoment k a t =
      ∑ q : Fin 4, alternatingWeight ((q.val + 1 : ℕ) : ℤ)
        ((3 - q.val + 1 - (a + t) : ℕ) : ℤ) (k + 2) := by
  have e := congrArg (fun n : ℕ => (n : ℤ)) (anchorMoment_nat 3 k a t)
  simpa only [anchorMoment, Nat.cast_sum, Nat.cast_mul, natCast_weight] using e

private def differenceWeight (j : Fin 3) : ℤ :=
  if j.val = 1 then -2 else 1

private theorem second_difference (A a : ℕ) :
    (∑ j : Fin 3, differenceWeight j * ((A - (a + j.val) : ℕ) : ℤ)) =
      if A = a + 1 then 1 else 0 := by
  rw [Fin.sum_univ_three]
  simp only [differenceWeight]
  change (1 : ℤ) * (A - (a + 0) : ℕ) + (-2) * (A - (a + 1) : ℕ) +
    1 * (A - (a + 2) : ℕ) = if A = a + 1 then 1 else 0
  split <;> omega

private def frequency (k a t : ℕ) : ℤ :=
  ∑ p : Profile 3 (k + 1),
    (if b p = a + 1 then (1 : ℤ) else 0) * (if b (flip p) = t + 1 then 1 else 0)

private theorem frequency_from_moments (k a t : ℕ) :
    frequency k a t = ∑ j : Fin 3, ∑ l : Fin 3,
      (differenceWeight j * differenceWeight l) * anchorMoment k (a + j.val) (t + l.val) := by
  unfold frequency anchorMoment
  simp_rw [← second_difference, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro p _
  ring

private theorem weight_zero_left (t : ℤ) (n : ℕ) :
    alternatingWeight 0 t (n + 2) = 0 := by
  unfold alternatingWeight
  rw [zero_pow (by omega), zero_mul]

private theorem weight_zero_right (a : ℤ) (n : ℕ) :
    alternatingWeight a 0 (n + 2) = 0 := by
  unfold alternatingWeight
  rw [zero_pow (by omega), mul_zero]

private theorem select_size (A : ℕ) (h₁ : 0 < A) (h₂ : A ≤ 4) (f : Fin 4 → ℤ) :
    (∑ a : Fin 4, (if A = a.val + 1 then (1 : ℤ) else 0) * f a) =
      f ⟨A - 1, by omega⟩ := by
  let i : Fin 4 := ⟨A - 1, by omega⟩
  have hi : A = i.val + 1 := by dsimp only [i]; omega
  change _ = f i
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left hi, one_mul]
  · intro j _ hj
    have hn : A ≠ j.val + 1 := by
      intro h
      exact hj (Fin.ext (by omega))
    rw [ite_eq_right hn, zero_mul]
  · simp

private theorem fiber_bound_four {k : ℕ} (p : Profile 3 (k + 1)) : b p ≤ 4 :=
  (fiber_bound p).trans (Nat.succ_le_of_lt (p 0).isLt)

private theorem profileCount_select {k : ℕ} (p : Profile 3 (k + 1)) (n : ℕ) :
    (∑ a : Fin 4, ∑ t : Fin 4,
      (if b p = a.val + 1 then (1 : ℤ) else 0) *
        ((if b (flip p) = t.val + 1 then (1 : ℤ) else 0) *
          alternatingWeight ((a.val + 1 : ℕ) : ℤ) ((t.val + 1 : ℕ) : ℤ) (n + 2))) =
       (profileCount p (n + 2) : ℤ) := by
  rw [profileCount_weight, natCast_weight]
  by_cases ha : b p = 0
  · simp [ha, weight_zero_left]
  by_cases ht : b (flip p) = 0
  · simp [ht, weight_zero_right]
  have hposA : 0 < b p := Nat.pos_of_ne_zero ha
  have hposT : 0 < b (flip p) := Nat.pos_of_ne_zero ht
  simp_rw [← Finset.mul_sum, select_size _ hposT (fiber_bound_four (flip p))]
  rw [select_size _ hposA (fiber_bound_four p)]
  have hA : b p - 1 + 1 = b p := by omega
  have hT : b (flip p) - 1 + 1 = b (flip p) := by omega
  simp only [hA, hT]

private theorem grouped_rectangular (n k : ℕ) :
    (C 4 5 (n + 1) (k + 1) : ℤ) = 2 * ∑ a : Fin 4, ∑ t : Fin 4,
      frequency k a.val t.val *
        alternatingWeight ((a.val + 1 : ℕ) : ℤ) ((t.val + 1 : ℕ) : ℤ) (n + 2) := by
  rw [show C 4 5 (n + 1) (k + 1) =
      2 * ∑ p : Profile 3 (k + 1), profileCount p (n + 2) from literal_sum 4 3 n k (by decide),
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  congr 1
  unfold frequency
  simp_rw [Finset.sum_mul, mul_assoc]
  conv_rhs =>
    arg 2
    intro a
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact (profileCount_select p n).symm

private def squareSequence (n : ℕ) : ℤ := C 4 5 (n + 1) (n + 1)

private def horizontalSlots (a t : Fin 4) (j l : Fin 3) (q : Fin 4) : ℕ :=
  3 - q.val + 1 - ((a.val + j.val) + (t.val + l.val))

private def spectralTerm (a t : Fin 4) (j l : Fin 3) (q : Fin 4) (n : ℕ) : ℤ :=
  (differenceWeight j * differenceWeight l *
    alternatingWeight ((q.val + 1 : ℕ) : ℤ) (horizontalSlots a t j l q : ℤ) (n + 2)) *
    alternatingWeight ((a.val + 1 : ℕ) : ℤ) ((t.val + 1 : ℕ) : ℤ) (n + 2)

private theorem squareSequence_expansion :
    squareSequence = (2 : ℤ) • (∑ a : Fin 4, ∑ t : Fin 4, ∑ j : Fin 3, ∑ l : Fin 3,
      ∑ q : Fin 4, spectralTerm a t j l q) := by
  funext n
  unfold squareSequence
  rw [grouped_rectangular n n]
  simp only [Pi.smul_apply, zsmul_eq_mul, Finset.sum_apply, Int.cast_ofNat]
  congr 1
  simp_rw [frequency_from_moments, anchorMoment_formula, Finset.mul_sum, Finset.sum_mul]
  rfl

private def spectralBase (a t : Fin 4) (j l : Fin 3) (q : Fin 4) : ℕ :=
  (q.val + 1) * horizontalSlots a t j l q * (a.val + 1) * (t.val + 1)

private theorem spectralTerm_step (a t : Fin 4) (j l : Fin 3) (q : Fin 4) (n : ℕ) :
    spectralTerm a t j l q (n + 2) = (spectralBase a t j l q : ℤ) * spectralTerm a t j l q n := by
  unfold spectralTerm spectralBase
  simp only [alternatingWeight_step _ _ (n + 2)]
  push_cast
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem spectral_cases :
    ∀ (a t : Fin 4) (j l : Fin 3) (q : Fin 4),
      horizontalSlots a t j l q = 0 ∨
      (a.val = 0 ∧ t.val = 0 ∧ q.val = 0 ∧ horizontalSlots a t j l q = 1) ∨
      spectralBase a t j l q = 2 ∨ spectralBase a t j l q = 3 ∨
      spectralBase a t j l q = 4 ∨ spectralBase a t j l q = 6 ∨ spectralBase a t j l q = 8 := by
  decide

private def P11 : ℤ[X] :=
  X ^ 11 - (Polynomial.C 1 * X ^ 10 + Polynomial.C 23 * X ^ 9 +
    Polynomial.C (-23) * X ^ 8 + Polynomial.C (-200) * X ^ 7 +
    Polynomial.C 200 * X ^ 6 + Polynomial.C 820 * X ^ 5 +
    Polynomial.C (-820) * X ^ 4 + Polynomial.C (-1584) * X ^ 3 +
    Polynomial.C 1584 * X ^ 2 + Polynomial.C 1152 * X ^ 1 + Polynomial.C (-1152) * X ^ 0)

private def factors11 : List ℤ[X] :=
  [linear 1, quadratic 2, quadratic 3, quadratic 4, quadratic 6, quadratic 8]

private theorem P11_factorization : P11 = factors11.prod := by
  simp only [P11, factors11, List.prod_cons, List.prod_nil, linear, quadratic, Polynomial.C_1,
    map_neg, Polynomial.C_ofNat]
  ring

private theorem spectralTerm_annihilated (a t : Fin 4) (j l : Fin 3) (q : Fin 4) :
    Kills P11 (spectralTerm a t j l q) := by
  rw [P11_factorization]
  rcases spectral_cases a t j l q with hz | ⟨ha, ht, hq, hs⟩ | h | h | h | h | h
  · have e : spectralTerm a t j l q = 0 := by
      funext n
      simp [spectralTerm, hz, weight_zero_right]
    rw [e]
    exact kills_zero _
  · have hStep (n : ℕ) : spectralTerm a t j l q (n + 1) = 1 * spectralTerm a t j l q n := by
      simp [spectralTerm, ha, ht, hq, hs, alternatingWeight]
    exact kills_of_dvd (List.dvd_prod (by simp [factors11]))
      (show Kills (linear 1) (spectralTerm a t j l q) by
        simpa only [linear, pow_one] using kills_step hStep)
  all_goals
    apply kills_of_dvd (Q := quadratic (spectralBase a t j l q : ℤ))
    · apply List.dvd_prod
      norm_num [factors11, h]
    · exact kills_step (spectralTerm_step a t j l q)

private theorem squareSequence_annihilated : Kills P11 squareSequence := by
  rw [squareSequence_expansion]
  exact kills_smul _ (kills_sum _ fun a => kills_sum _ fun t =>
    kills_sum _ fun j => kills_sum _ fun l => kills_sum _ fun q =>
      spectralTerm_annihilated a t j l q)

private theorem kills_P11_iff (f : Sequence) :
    Kills P11 f ↔ ∀ n : ℕ, f (n + 11) =
      f (n + 10) + 23 * f (n + 9) - 23 * f (n + 8) - 200 * f (n + 7) +
      200 * f (n + 6) + 820 * f (n + 5) - 820 * f (n + 4) - 1584 * f (n + 3) +
      1584 * f (n + 2) + 1152 * f (n + 1) - 1152 * f n := by
  unfold Kills P11
  rw [funext_iff]
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply,
    Pi.add_apply, Pi.zero_apply, eval_C_mul_X_pow, map_pow, aeval_X, shift_pow_apply,
    Nat.add_zero, sub_eq_zero]
  constructor <;> intro h n <;> have hn := h n <;> linarith

/-- The signed order-eleven recurrence for every positive index, including the window 1 through 12. -/
theorem a235270_order11 (n : ℕ) (hn : 1 ≤ n) :
    (C 4 5 (n + 11) (n + 11) : ℤ) =
      (C 4 5 (n + 10) (n + 10) : ℤ) + 23 * (C 4 5 (n + 9) (n + 9) : ℤ) - 23 * (C 4 5 (n + 8) (n + 8) : ℤ) -
      200 * (C 4 5 (n + 7) (n + 7) : ℤ) + 200 * (C 4 5 (n + 6) (n + 6) : ℤ) + 820 * (C 4 5 (n + 5) (n + 5) : ℤ) -
      820 * (C 4 5 (n + 4) (n + 4) : ℤ) - 1584 * (C 4 5 (n + 3) (n + 3) : ℤ) + 1584 * (C 4 5 (n + 2) (n + 2) : ℤ) +
      1152 * (C 4 5 (n + 1) (n + 1) : ℤ) - 1152 * (C 4 5 n n : ℤ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := (kills_P11_iff squareSequence).mp squareSequence_annihilated m
  simpa only [squareSequence, ← Nat.add_assoc, Nat.add_comm 1] using h

end
end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence
