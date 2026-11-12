/- GID: D5/S0/Certificates/Combinatorics/NormalizedPfaffian
   generality: G
   mirror-B: D5/B/S0/Certificates/Combinatorics/NormalizedPfaffian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.GroupTheory.Perm.Fin, mathlib/module/Mathlib.GroupTheory.Perm.Sign]
   utility: none
   digest: The original normalized Pfaffian pair-listing core and its counted crossing convention bridge over arbitrary commutative rings. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation

/-- A partner map: its two-element orbits are precisely unordered pair partitions.
The paper's labels 1,...,2k are shifted down by one. -/
abbrev P (k : ℕ) := {p : Fin (2 * k) → Fin (2 * k) //
  Function.Involutive p ∧ ∀ x, p x ≠ x}
/-- The partner map of (1 2 | 3 4 | ...). -/
def ep (k : ℕ) (x : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by
    have := x.isLt
    split <;> omega⟩

def e (k : ℕ) : P k := ⟨ep k, by
  constructor
  · intro x
    apply Fin.ext
    simp only [ep]
    split <;> split <;> omega
  · intro x h
    have hh := congrArg Fin.val h
    simp only [ep] at hh
    split at hh <;> omega⟩

end D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation


namespace D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation

/-- The unique representative convention for listings: orient each pair increasingly,
then order pairs by their first endpoint. -/
def normalizedListings (n : ℕ) : Finset (Equiv.Perm (Fin (2 * n))) :=
  (Finset.univ : Finset (Equiv.Perm (Fin (2 * n)))).filter (fun σ =>
      (∀ i : Fin n, σ ⟨2 * i.val, by omega⟩ < σ ⟨2 * i.val + 1, by omega⟩) ∧
      ∀ i j : Fin n, i < j → σ ⟨2 * i.val, by omega⟩ < σ ⟨2 * j.val, by omega⟩)

/-- The Pfaffian as defined in the source: the sum, over the partitions of `[2n]` into
two-element subsets `{σ(2i), σ(2i+1)}`, of the sign of the listing permutation `σ` times the
product of the paired entries. Each partition is listed once, with increasing pairs ordered by
their first elements. -/
def pfaffian {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) : R :=
  ∑ σ ∈ normalizedListings n,
    ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin n, A (σ ⟨2 * i.val, by omega⟩) (σ ⟨2 * i.val + 1, by omega⟩)

end D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation


namespace D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing

open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P e ep)
open D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation (normalizedListings)

def first {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by omega⟩
def second {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩

private def lows {n : ℕ} (p : P n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun x => x < p.val x)

private theorem lows_card {n : ℕ} (p : P n) : (lows p).card = n := by
  have himage : (lows p).image p.val = Finset.univ.filter (fun x => ¬ x < p.val x) := by
    ext x
    simp only [Finset.mem_image, lows, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [p.property.1 y] using not_lt_of_gt hy
    · intro hx
      refine ⟨p.val x, ?_, p.property.1 x⟩
      rw [p.property.1 x]
      exact lt_of_le_of_ne (le_of_not_gt hx) (p.property.2 x)
  have hi := Finset.card_image_of_injective (lows p) p.property.1.injective
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * n))))
    (fun x => x < p.val x)
  rw [← himage, hi] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change (lows p).card + (lows p).card = 2 * n at hc
  omega

private def lower {n : ℕ} (p : P n) (i : Fin n) : Fin (2 * n) :=
  (lows p).orderEmbOfFin (lows_card p) i

private theorem lower_lt {n : ℕ} (p : P n) (i : Fin n) :
    lower p i < p.val (lower p i) := by
  exact (Finset.mem_filter.mp ((lows p).orderEmbOfFin_mem (lows_card p) i)).2

private theorem lower_injective {n : ℕ} (p : P n) : Function.Injective (lower p) :=
  ((lows p).orderEmbOfFin (lows_card p)).injective

private def flatten {n : ℕ} (p : P n) (x : Fin (2 * n)) : Fin (2 * n) :=
  if x.val % 2 = 0 then lower p ⟨x.val / 2, by omega⟩
  else p.val (lower p ⟨x.val / 2, by omega⟩)

private theorem flatten_bijective {n : ℕ} (p : P n) : Function.Bijective (flatten p) := by
  constructor
  · intro x y h
    unfold flatten at h
    split_ifs at h with hx hy hy
    · have he := lower_injective p h
      have hv := congrArg Fin.val he
      change x.val / 2 = y.val / 2 at hv
      apply Fin.ext
      omega
    · have hn := lower_lt p ⟨x.val / 2, by omega⟩
      have hm := lower_lt p ⟨y.val / 2, by omega⟩
      rw [h, p.property.1] at hn
      exact (lt_asymm hn hm).elim
    · have hn := lower_lt p ⟨x.val / 2, by omega⟩
      have hm := lower_lt p ⟨y.val / 2, by omega⟩
      rw [← h, p.property.1] at hm
      exact (lt_asymm hn hm).elim
    · have he := lower_injective p (p.property.1.injective h)
      have hv := congrArg Fin.val he
      change x.val / 2 = y.val / 2 at hv
      apply Fin.ext
      omega
  · intro x
    by_cases hx : x < p.val x
    · have hmem : x ∈ lows p := by simp [lows, hx]
      obtain ⟨i, hi⟩ := (lows p).orderIsoOfFin (lows_card p) |>.surjective ⟨x, hmem⟩
      refine ⟨first i, ?_⟩
      have hlo : lower p i = x := congrArg Subtype.val hi
      simpa [flatten, first, Nat.mul_div_right] using hlo
    · have hmem : p.val x ∈ lows p := by
        simp only [lows, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [p.property.1]
        exact lt_of_le_of_ne (le_of_not_gt hx) (p.property.2 x)
      obtain ⟨i, hi⟩ := (lows p).orderIsoOfFin (lows_card p) |>.surjective ⟨p.val x, hmem⟩
      refine ⟨second i, ?_⟩
      have hlo : lower p i = p.val x := congrArg Subtype.val hi
      simpa [flatten, second, hlo, Nat.add_div, p.property.1] using p.property.1 x

/-- Increasing pairs, ordered by their first endpoint. -/
noncomputable def canonicalListing {n : ℕ} (p : P n) : Equiv.Perm (Fin (2 * n)) :=
  Equiv.ofBijective (flatten p) (flatten_bijective p)


private theorem canonical_first {n : ℕ} (p : P n) (i : Fin n) :
    canonicalListing p (first i) = lower p i := by
  simp [canonicalListing, flatten, first]

private theorem canonical_second {n : ℕ} (p : P n) (i : Fin n) :
    canonicalListing p (second i) = p.val (lower p i) := by
  simp [canonicalListing, flatten, second, Nat.add_div]

private theorem e_first {n : ℕ} (i : Fin n) : (e n).val (first i) = second i := by
  apply Fin.ext
  simp [e, ep, first, second]

private theorem e_second {n : ℕ} (i : Fin n) : (e n).val (second i) = first i := by
  apply Fin.ext
  simp [e, ep, first, second]

theorem index_cases {n : ℕ} (x : Fin (2 * n)) :
    ∃ i : Fin n, x = first i ∨ x = second i := by
  refine ⟨⟨x.val / 2, by omega⟩, ?_⟩
  by_cases hx : x.val % 2 = 0
  · left; apply Fin.ext; simp only [first]; omega
  · right; apply Fin.ext; simp only [second]; omega

private theorem canonical_intertwines {n : ℕ} (p : P n) (x : Fin (2 * n)) :
    canonicalListing p ((e n).val x) = p.val (canonicalListing p x) := by
  obtain ⟨i, rfl | rfl⟩ := index_cases x
  · rw [e_first, canonical_first, canonical_second]
  · rw [e_second, canonical_first, canonical_second, p.property.1]

private theorem canonical_normalized {n : ℕ} (p : P n) :
    canonicalListing p ∈ normalizedListings n := by
  simp only [normalizedListings, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro i
    change canonicalListing p (first i) < canonicalListing p (second i)
    rw [canonical_first, canonical_second]
    exact lower_lt p i
  · intro i j hij
    change canonicalListing p (first i) < canonicalListing p (first j)
    rw [canonical_first, canonical_first]
    exact ((lows p).orderEmbOfFin (lows_card p)).strictMono hij

/-- A listing represents the pairing obtained by conjugating consecutive pairs. -/
def pairingOfListing {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) : P n :=
  ⟨fun x => s ((e n).val (s.symm x)), by
    constructor
    · intro x
      simp only [s.symm_apply_apply]
      rw [(e n).property.1, s.apply_symm_apply]
    · intro x h
      have he := congrArg s.symm h
      simp only [s.symm_apply_apply] at he
      exact (e n).property.2 (s.symm x) he⟩

private theorem pairing_first {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    (pairingOfListing s).val (s (first i)) = s (second i) := by
  simp only [pairingOfListing, s.symm_apply_apply, e_first]

private theorem pairing_canonical {n : ℕ} (p : P n) :
    pairingOfListing (canonicalListing p) = p := by
  apply Subtype.ext
  funext x
  obtain ⟨y, rfl⟩ := (canonicalListing p).surjective x
  simp only [pairingOfListing, Equiv.symm_apply_apply]
  exact canonical_intertwines p y

private theorem canonical_pairing {n : ℕ} (s : Equiv.Perm (Fin (2 * n)))
    (hs : s ∈ normalizedListings n) : canonicalListing (pairingOfListing s) = s := by
  have hn := (Finset.mem_filter.mp hs).2
  have hf : (fun i => s (first i)) = lower (pairingOfListing s) := by
    apply Finset.orderEmbOfFin_unique (lows_card (pairingOfListing s))
    · intro i
      simp only [lows, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [pairing_first]
      exact hn.1 i
    · intro i j hij
      exact hn.2 i j hij
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl | rfl⟩ := index_cases x
  · rw [canonical_first]
    exact (congrFun hf i).symm
  · rw [canonical_second, ← congrFun hf i, pairing_first]

/-- Normalized permutations list all pair partitions exactly once. -/
noncomputable def listingEquiv (n : ℕ) :
    {s : Equiv.Perm (Fin (2 * n)) // s ∈ normalizedListings n} ≃ P n where
  toFun s := pairingOfListing s.val
  invFun p := ⟨canonicalListing p, canonical_normalized p⟩
  left_inv s := Subtype.ext (canonical_pairing s.val s.property)
  right_inv := pairing_canonical


/-- The two adjacent slots of a canonical listing are actual partners. -/
theorem canonical_mate {n : ℕ} (p : P n) (i : Fin n) :
    p.val (canonicalListing p ⟨2 * i.val, by omega⟩) =
      canonicalListing p ⟨2 * i.val + 1, by omega⟩ := by
  change p.val (canonicalListing p (first i)) = canonicalListing p (second i)
  rw [canonical_first, canonical_second]


private theorem pairing_second {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    (pairingOfListing s).val (s (second i)) = s (first i) := by
  simp only [pairingOfListing, s.symm_apply_apply, e_second]

/-- A listing represents a partner map exactly when every consecutive pair does. -/
theorem pairing_eq_iff {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (p : P n) :
    pairingOfListing s = p ↔
      ∀ i : Fin n, p.val (s ⟨2 * i.val, by omega⟩) = s ⟨2 * i.val + 1, by omega⟩ := by
  constructor
  · rintro rfl i
    exact pairing_first s i
  · intro h
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := s.surjective x
    obtain ⟨i, rfl | rfl⟩ := index_cases y
    · exact (pairing_first s i).trans (h i).symm
    · rw [pairing_second]
      exact (p.property.1 _).symm.trans (congrArg p.val (h i))

private theorem distinct_slots {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    s (first i) ≠ s (second i) := by
  intro h
  have hi := congrArg Fin.val (s.injective h)
  simp only [first, second] at hi
  omega

private theorem min_partner {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    (pairingOfListing s).val (min (s (first i)) (s (second i))) =
      max (s (first i)) (s (second i)) := by
  by_cases h : s (first i) ≤ s (second i)
  · rw [min_eq_left h, max_eq_right h, pairing_first]
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), pairing_second]

private theorem min_low {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    min (s (first i)) (s (second i)) ∈ lows (pairingOfListing s) := by
  simp only [lows, Finset.mem_filter, Finset.mem_univ, true_and, min_partner]
  exact min_lt_max.mpr (distinct_slots s i)

private def pairIndex {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) : Fin n :=
  ((lows (pairingOfListing s)).orderIsoOfFin (lows_card (pairingOfListing s))).symm
    ⟨min (s (first i)) (s (second i)), min_low s i⟩

private theorem pairIndex_injective {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    Function.Injective (pairIndex s) := by
  intro i j hij
  have he := congrArg
    (fun k =>
      ((lows (pairingOfListing s)).orderIsoOfFin (lows_card (pairingOfListing s)) k).val) hij
  simp only [pairIndex, OrderIso.apply_symm_apply] at he
  by_cases hi : s (first i) ≤ s (second i) <;>
    by_cases hj : s (first j) ≤ s (second j)
  · rw [min_eq_left hi, min_eq_left hj] at he
    have hh := congrArg Fin.val (s.injective he)
    apply Fin.ext
    simp only [first] at hh
    omega
  · rw [min_eq_left hi, min_eq_right (le_of_not_ge hj)] at he
    have hh := congrArg Fin.val (s.injective he)
    simp only [first, second] at hh
    omega
  · rw [min_eq_right (le_of_not_ge hi), min_eq_left hj] at he
    have hh := congrArg Fin.val (s.injective he)
    simp only [first, second] at hh
    omega
  · rw [min_eq_right (le_of_not_ge hi), min_eq_right (le_of_not_ge hj)] at he
    have hh := congrArg Fin.val (s.injective he)
    apply Fin.ext
    simp only [second] at hh
    omega

private noncomputable def pairOrder {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm (Fin n) := Equiv.ofBijective (pairIndex s)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨pairIndex_injective s, rfl⟩)

private theorem canonical_pairOrder_first {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    canonicalListing (pairingOfListing s) (first (pairOrder s i)) =
      min (s (first i)) (s (second i)) := by
  rw [canonical_first]
  exact congrArg Subtype.val
    (((lows (pairingOfListing s)).orderIsoOfFin (lows_card (pairingOfListing s))).apply_symm_apply
      ⟨min (s (first i)) (s (second i)), min_low s i⟩)

private theorem canonical_pairOrder_second {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    canonicalListing (pairingOfListing s) (second (pairOrder s i)) =
      max (s (first i)) (s (second i)) := by
  rw [canonical_second, ← canonical_first, canonical_pairOrder_first, min_partner]

private def slots (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

private theorem slots_zero {n : ℕ} (i : Fin n) : slots n (i, 0) = first i := by
  apply Fin.ext
  simp [slots, first]

private theorem slots_one {n : ℕ} (i : Fin n) : slots n (i, 1) = second i := by
  apply Fin.ext
  simp [slots, second, Nat.add_comm]

private def turn {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin n) : Equiv.Perm (Fin 2) :=
  if s (first i) ≤ s (second i) then 1 else Equiv.swap 0 1

private noncomputable def reordering {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm (Fin (2 * n)) :=
  (slots n).permCongr
    (Equiv.prodCongr (pairOrder s) (1 : Equiv.Perm (Fin 2)) * Equiv.prodCongrRight (turn s))

private theorem listing_reordering {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    s = canonicalListing (pairingOfListing s) * reordering s := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, b⟩, rfl⟩ := (slots n).surjective x
  fin_cases b <;>
    simp only [reordering, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.Perm.mul_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.prodCongrRight_apply,
      Equiv.Perm.one_apply, turn] <;>
    split_ifs with hi
  · change s (slots n (i, 0)) =
      canonicalListing (pairingOfListing s) (slots n (pairOrder s i, 0))
    rw [slots_zero, slots_zero, canonical_pairOrder_first, min_eq_left hi]
  · change s (slots n (i, 0)) =
      canonicalListing (pairingOfListing s) (slots n (pairOrder s i, 1))
    rw [slots_zero, slots_one, canonical_pairOrder_second, max_eq_left (le_of_not_ge hi)]
  · change s (slots n (i, 1)) =
      canonicalListing (pairingOfListing s) (slots n (pairOrder s i, 1))
    rw [slots_one, slots_one, canonical_pairOrder_second, max_eq_right hi]
  · change s (slots n (i, 1)) =
      canonicalListing (pairingOfListing s) (slots n (pairOrder s i, 0))
    rw [slots_one, slots_zero, canonical_pairOrder_first, min_eq_right (le_of_not_ge hi)]


private theorem sign_reordering {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm.sign (reordering s) = ∏ i : Fin n, Equiv.Perm.sign (turn s i) := by
  have hb : Equiv.Perm.sign
      (Equiv.prodCongr (pairOrder s) (1 : Equiv.Perm (Fin 2))) = 1 := by
    change Equiv.Perm.sign (Equiv.prodCongrLeft (fun _ : Fin 2 => pairOrder s)) = 1
    rw [Equiv.Perm.sign_prodCongrLeft, Fin.prod_univ_two]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (pairOrder s)) with h | h <;> simp [h]
  simp only [reordering, Equiv.Perm.sign_permCongr, map_mul, hb,
    Equiv.Perm.sign_prodCongrRight, one_mul]

/-- The signed unit factor of one oriented listing. -/
def listingValue {n : ℕ} (f : Fin (2 * n) → Fin (2 * n) → ℤˣ)
    (s : Equiv.Perm (Fin (2 * n))) : ℤˣ :=
  Equiv.Perm.sign s * ∏ i : Fin n, f (s (first i)) (s (second i))

/-- Reordering pairs and reversing individual pairs preserve the signed unit factor. -/
theorem listing_value_canonical {n : ℕ} (f : Fin (2 * n) → Fin (2 * n) → ℤˣ)
    (hf : ∀ x y, x ≠ y → f y x = -f x y) (s : Equiv.Perm (Fin (2 * n))) :
    listingValue f s = listingValue f (canonicalListing (pairingOfListing s)) := by
  have hpoint (i : Fin n) :
      f (s (first i)) (s (second i)) = Equiv.Perm.sign (turn s i) *
        f (canonicalListing (pairingOfListing s) (first (pairOrder s i)))
          (canonicalListing (pairingOfListing s) (second (pairOrder s i))) := by
    rw [canonical_pairOrder_first, canonical_pairOrder_second]
    by_cases h : s (first i) ≤ s (second i)
    · simp [turn, h]
    · have hrev := hf (s (first i)) (s (second i)) (distinct_slots s i)
      simp only [turn, ite_eq_right h, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1),
        min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), neg_one_mul]
      rw [hrev, neg_neg]
  have hp : (∏ i : Fin n, f (s (first i)) (s (second i))) =
      Equiv.Perm.sign (reordering s) *
        ∏ i : Fin n, f (canonicalListing (pairingOfListing s) (first i))
          (canonicalListing (pairingOfListing s) (second i)) := by
    simp_rw [hpoint]
    rw [Finset.prod_mul_distrib, ← sign_reordering]
    congr 1
    exact Equiv.prod_comp (pairOrder s) (fun i : Fin n =>
      f (canonicalListing (pairingOfListing s) (first i))
        (canonicalListing (pairingOfListing s) (second i)))
  have hs := congrArg Equiv.Perm.sign (listing_reordering s)
  rw [map_mul] at hs
  unfold listingValue
  rw [hs, hp]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (reordering s)) with h | h <;>
    simp [h]

end D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing


namespace D5.S0.Certificates.Combinatorics.NormalizedPfaffianCount

open D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P)
open D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing

abbrev Pos (n : ℕ) := Fin (2 * n)
abbrev Pair (n : ℕ) := Pos n × Pos n

/-- Positions of a listing that form an inversion. -/
def inversionPairs {n : ℕ} (s : Equiv.Perm (Pos n)) : Finset (Pair n) :=
  Finset.univ.filter (fun q => q.1 < q.2 ∧ s q.2 < s q.1)

/-- Lower endpoints of the partner pairs. -/
def lowerEndpoints {n : ℕ} (p : P n) : Finset (Pos n) :=
  Finset.univ.filter (fun a => a < p.val a)

/-- Ordered lower-endpoint pairs whose arcs cross. -/
def crossingPairs {n : ℕ} (p : P n) : Finset (Pair n) :=
  Finset.univ.filter (fun q =>
    q.1 ∈ lowerEndpoints p ∧ q.2 ∈ lowerEndpoints p ∧
      q.1 < q.2 ∧ q.2 < p.val q.1 ∧ p.val q.1 < p.val q.2)

/-- Ordered lower-endpoint pairs whose arcs are nested. -/
def nestingPairs {n : ℕ} (p : P n) : Finset (Pair n) :=
  Finset.univ.filter (fun q =>
    q.1 ∈ lowerEndpoints p ∧ q.2 ∈ lowerEndpoints p ∧
      q.1 < q.2 ∧ q.2 < p.val q.2 ∧ p.val q.2 < p.val q.1)

abbrev InvType {n : ℕ} (s : Equiv.Perm (Pos n)) := {q : Pair n // q ∈ inversionPairs s}
abbrev CrossType {n : ℕ} (p : P n) := {q : Pair n // q ∈ crossingPairs p}
abbrev NestType {n : ℕ} (p : P n) := {q : Pair n // q ∈ nestingPairs p}

private def slotIndex {n : ℕ} (x : Pos n) : Fin n :=
  ⟨x.val / 2, by omega⟩

private theorem slot_cases {n : ℕ} (x : Pos n) :
    x = first (slotIndex x) ∨ x = second (slotIndex x) := by
  by_cases h : x.val % 2 = 0
  · left
    apply Fin.ext
    simp [slotIndex, first]
    omega
  · right
    apply Fin.ext
    simp [slotIndex, second]
    omega

private theorem first_slot_value {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (i : Fin n) :
    s (first i) < s (second i) := by
  exact (Finset.mem_filter.mp hs).2.1 i

private theorem first_slots_order {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (i j : Fin n) (hij : i < j) :
    s (first i) < s (first j) := by
  exact (Finset.mem_filter.mp hs).2.2 i j hij

private theorem pairing_slot {n : ℕ} (s : Equiv.Perm (Pos n))
    (i : Fin n) :
    (pairingOfListing s).val (s (first i)) = s (second i) := by
  exact (pairing_eq_iff s (pairingOfListing s)).mp rfl i

private theorem pairing_slot_second {n : ℕ} (s : Equiv.Perm (Pos n))
    (i : Fin n) :
    (pairingOfListing s).val (s (second i)) = s (first i) := by
  rw [← pairing_slot s i, (pairingOfListing s).property.1]

private theorem lower_rep {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (a : Pos n)
    (ha : a < (pairingOfListing s).val a) :
    ∃ i : Fin n, a = s (first i) := by
  have hcases := slot_cases (s.symm a)
  rcases hcases with hi | hi
  · refine ⟨slotIndex (s.symm a), ?_⟩
    rw [← hi]
    simp
  · exfalso
    have hia : a = s (second (slotIndex (s.symm a))) := by
      rw [← hi]
      simp
    have hpa : (pairingOfListing s).val a = s (first (slotIndex (s.symm a))) := by
      calc
        (pairingOfListing s).val a = (pairingOfListing s).val
            (s (second (slotIndex (s.symm a)))) := congrArg (pairingOfListing s).val hia
        _ = s (first (slotIndex (s.symm a))) := pairing_slot_second s (slotIndex (s.symm a))
    have hlt := first_slot_value s hs (slotIndex (s.symm a))
    rw [hia, pairing_slot_second] at ha
    exact (not_lt_of_ge (le_of_lt hlt)) ha

private theorem lower_rep_unique {n : ℕ} (s : Equiv.Perm (Pos n))
    {i j : Fin n} {a : Pos n} (hi : a = s (first i)) (hj : a = s (first j)) : i = j := by
  apply Fin.ext
  have h := s.injective (hi.symm.trans hj)
  have hv := congrArg Fin.val h
  change 2 * i.val = 2 * j.val at hv
  omega

private noncomputable def lowerIndex {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (a : Pos n)
    (ha : a < (pairingOfListing s).val a) : Fin n :=
  Classical.choose (lower_rep s hs a ha)

private theorem lowerIndex_spec {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (a : Pos n)
    (ha : a < (pairingOfListing s).val a) :
    a = s (first (lowerIndex s hs a ha)) := by
  exact Classical.choose_spec (lower_rep s hs a ha)

private theorem lowerIndex_eq {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (a : Pos n)
    (ha : a < (pairingOfListing s).val a) {i : Fin n}
    (hi : a = s (first i)) :
    lowerIndex s hs a ha = i := by
  apply lower_rep_unique s (lowerIndex_spec s hs a ha) hi

private theorem inversion_first_even_false {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) {q : InvType s}
    {i : Fin n} (hqi : q.val.1 = first i) : False := by
  have hq := q.property
  simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  rw [hqi] at hq
  rcases slot_cases q.val.2 with hj | hj
  · rw [hj] at hq
    have hij : i < slotIndex q.val.2 := by
      have hpos := hq.1
      change 2 * i.val < 2 * (slotIndex q.val.2).val at hpos
      omega
    exact lt_asymm (first_slots_order s hs i _ hij) hq.2
  · rw [hj] at hq
    have hij : i ≤ slotIndex q.val.2 := by
      have hpos := hq.1
      change 2 * i.val < 2 * (slotIndex q.val.2).val + 1 at hpos
      omega
    have hm : Monotone (fun k : Fin n => s (first k)) :=
      (show StrictMono (fun k : Fin n => s (first k)) from first_slots_order s hs).monotone
    exact lt_asymm ((hm hij).trans_lt (first_slot_value s hs _)) hq.2

private theorem inversion_slot_order {n : ℕ} (s : Equiv.Perm (Pos n))
    {q : InvType s} {i j : Fin n} (hqi : q.val.1 = second i)
    (hqj : q.val.2 = first j ∨ q.val.2 = second j) : i < j := by
  have hq := q.property
  simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  rw [hqi] at hq
  rcases hqj with hj | hj
  · rw [hj] at hq
    have hpos := hq.1
    change 2 * i.val + 1 < 2 * j.val at hpos
    omega
  · rw [hj] at hq
    have hpos := hq.1
    change 2 * i.val + 1 < 2 * j.val + 1 at hpos
    omega

private theorem inversion_cross_data {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (q : InvType s) {i j : Fin n}
    (hqi : q.val.1 = second i) (hqj : q.val.2 = first j)
    (hij : i < j) (hupper : s (second i) < s (second j)) :
    (s (first i), s (first j)) ∈ crossingPairs (pairingOfListing s) := by
  have hq := q.property
  simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  rw [hqi, hqj] at hq
  have hlowi : s (first i) < (pairingOfListing s).val (s (first i)) := by
    rw [pairing_slot]
    exact first_slot_value s hs i
  have hlowj : s (first j) < (pairingOfListing s).val (s (first j)) := by
    rw [pairing_slot]
    exact first_slot_value s hs j
  simp only [crossingPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    lowerEndpoints, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hlowi
  · exact hlowj
  · exact first_slots_order s hs i j hij
  · simpa only [pairing_slot] using hq.2
  · simpa only [pairing_slot] using hupper

private theorem inversion_nest_data {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) {i j : Fin n}
    (hij : i < j) (hn : ¬ s (second i) < s (second j)) :
    (s (first i), s (first j)) ∈ nestingPairs (pairingOfListing s) := by
  have hne : s (second i) ≠ s (second j) := by
    intro h
    have hv := congrArg Fin.val (s.injective h)
    change 2 * i.val + 1 = 2 * j.val + 1 at hv
    omega
  have hji := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
  simp only [nestingPairs, lowerEndpoints, Finset.mem_filter, Finset.mem_univ,
    true_and, pairing_slot]
  exact ⟨first_slot_value s hs i, first_slot_value s hs j,
    first_slots_order s hs i j hij, first_slot_value s hs j, hji⟩

private theorem first_order_iff {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) {i j : Fin n} :
    s (first i) < s (first j) ↔ i < j := by
  constructor
  · intro h
    by_contra hn
    have hji : j < i := by
      have hne : i ≠ j := by
        intro hij
        subst j
        exact (lt_irrefl _ h)
      exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
    exact (not_lt_of_ge (le_of_lt (first_slots_order s hs j i hji))) h
  · exact first_slots_order s hs i j

noncomputable def inversionToTarget {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) (q : InvType s) :
    CrossType (pairingOfListing s) ⊕
      (NestType (pairingOfListing s) × Fin 2) := by
  classical
  by_cases hfirst : q.val.1 = first (slotIndex q.val.1)
  · exact (inversion_first_even_false s hs hfirst).elim
  · have hsecond : q.val.1 = second (slotIndex q.val.1) :=
      (slot_cases q.val.1).resolve_left hfirst
    by_cases hfirst2 : q.val.2 = first (slotIndex q.val.2)
    · let i := slotIndex q.val.1
      let j := slotIndex q.val.2
      have hij := inversion_slot_order s hsecond
        (Or.inl hfirst2)
      by_cases hupper : s (second i) < s (second j)
      · exact Sum.inl ⟨(s (first i), s (first j)),
          inversion_cross_data s hs q hsecond hfirst2 hij hupper⟩
      · exact Sum.inr ⟨⟨(s (first i), s (first j)),
          inversion_nest_data s hs hij hupper⟩, 0⟩
    · have hsecond2 : q.val.2 = second (slotIndex q.val.2) :=
        (slot_cases q.val.2).resolve_left hfirst2
      let i := slotIndex q.val.1
      let j := slotIndex q.val.2
      have hij := inversion_slot_order s hsecond
        (Or.inr hsecond2)
      have hq := q.property
      simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hsecond, hsecond2] at hq
      have hupper : ¬ s (second i) < s (second j) := by
        intro h
        exact (lt_asymm h hq.2)
      exact Sum.inr ⟨⟨(s (first i), s (first j)),
        inversion_nest_data s hs hij hupper⟩, 1⟩

private theorem cross_lower {n : ℕ} {s : Equiv.Perm (Pos n)}
    (hs : s ∈ normalizedListings n) (q : CrossType (pairingOfListing s)) :
    q.val.1 < (pairingOfListing s).val q.val.1 ∧
      q.val.2 < (pairingOfListing s).val q.val.2 ∧ q.val.1 < q.val.2 ∧
      q.val.2 < (pairingOfListing s).val q.val.1 ∧
      (pairingOfListing s).val q.val.1 < (pairingOfListing s).val q.val.2 := by
  simpa [crossingPairs, lowerEndpoints] using q.property

private theorem nest_lower {n : ℕ} {s : Equiv.Perm (Pos n)}
    (hs : s ∈ normalizedListings n) (q : NestType (pairingOfListing s)) :
    q.val.1 < (pairingOfListing s).val q.val.1 ∧
      q.val.2 < (pairingOfListing s).val q.val.2 ∧ q.val.1 < q.val.2 ∧
      q.val.2 < (pairingOfListing s).val q.val.2 ∧
      (pairingOfListing s).val q.val.2 < (pairingOfListing s).val q.val.1 := by
  simpa [nestingPairs, lowerEndpoints] using q.property

noncomputable def targetToInversion {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) :
    CrossType (pairingOfListing s) ⊕
      (NestType (pairingOfListing s) × Fin 2) → InvType s
  | Sum.inl q => by
      classical
      let i := lowerIndex s hs q.val.1 (cross_lower hs q).1
      let j := lowerIndex s hs q.val.2 (cross_lower hs q).2.1
      have hi : q.val.1 = s (first i) := lowerIndex_spec s hs q.val.1 (cross_lower hs q).1
      have hj : q.val.2 = s (first j) := lowerIndex_spec s hs q.val.2 (cross_lower hs q).2.1
      have hd := cross_lower hs q
      rw [hi, hj, pairing_slot, pairing_slot] at hd
      have hij := (first_order_iff s hs).mp hd.2.2.1
      refine ⟨(second i, first j), ?_⟩
      simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by change 2 * i.val + 1 < 2 * j.val; omega, hd.2.2.2.1⟩
  | Sum.inr (q, b) => by
      classical
      let i := lowerIndex s hs q.val.1 (nest_lower hs q).1
      let j := lowerIndex s hs q.val.2 (nest_lower hs q).2.1
      have hi : q.val.1 = s (first i) := lowerIndex_spec s hs q.val.1 (nest_lower hs q).1
      have hj : q.val.2 = s (first j) := lowerIndex_spec s hs q.val.2 (nest_lower hs q).2.1
      have hd := nest_lower hs q
      rw [hi, hj, pairing_slot, pairing_slot] at hd
      have hij := (first_order_iff s hs).mp hd.2.2.1
      by_cases hb : b = 0
      · refine ⟨(second i, first j), ?_⟩
        simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by change 2 * i.val + 1 < 2 * j.val; omega,
          hd.2.2.2.1.trans hd.2.2.2.2⟩
      · refine ⟨(second i, second j), ?_⟩
        simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by change 2 * i.val + 1 < 2 * j.val + 1; omega, hd.2.2.2.2⟩

private theorem slotIndex_first {n : ℕ} (i : Fin n) : slotIndex (first i) = i := by
  apply Fin.ext
  simp [slotIndex, first]

private theorem slotIndex_second {n : ℕ} (i : Fin n) : slotIndex (second i) = i := by
  apply Fin.ext
  simp [slotIndex, second, Nat.add_div]

private theorem second_ne_first {n : ℕ} (i j : Fin n) : second i ≠ first j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [first, second] at hv
  omega

/-- Every inversion of a normalized listing is one crossing or one of two nest orientations. -/
noncomputable def inversionCrossNestEquiv {n : ℕ} (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) :
    InvType s ≃ CrossType (pairingOfListing s) ⊕
      (NestType (pairingOfListing s) × Fin 2) where
  toFun := inversionToTarget s hs
  invFun := targetToInversion s hs
  left_inv := by
    intro q
    -- the slot decomposition is unique, so the constructed positions recover q
    apply Subtype.ext
    have hcases := slot_cases q.val.1
    rcases hcases with hfirst | hsecond
    · exact (inversion_first_even_false s hs hfirst).elim
    · have hnotfirst : ¬ q.val.1 = first (slotIndex q.val.1) := by
        intro h
        exact inversion_first_even_false s hs h
      let i := slotIndex q.val.1
      have hcases2 := slot_cases q.val.2
      rcases hcases2 with hfirst2 | hsecond2
      · let j := slotIndex q.val.2
        have hij := inversion_slot_order s hsecond (Or.inl hfirst2)
        by_cases hupper : s (second i) < s (second j)
        · rw [inversionToTarget]
          have hupper' : s (second (slotIndex q.val.1)) < s (second (slotIndex q.val.2)) := by
            simpa [i, j] using hupper
          simp only [dite_eq_right hnotfirst, dite_eq_left hfirst2, dite_eq_left hupper']
          rw [targetToInversion.eq_def]
          simp only [Sum.rec]
          have hli := lowerIndex_eq s hs (s (first i)) (by rw [pairing_slot]; exact first_slot_value s hs i) rfl
          have hlj := lowerIndex_eq s hs (s (first j)) (by rw [pairing_slot]; exact first_slot_value s hs j) rfl
          rw [hli, hlj]
          exact Prod.ext hsecond.symm hfirst2.symm
        · rw [inversionToTarget]
          have hupper' : ¬ s (second (slotIndex q.val.1)) < s (second (slotIndex q.val.2)) := by
            simpa [i, j] using hupper
          simp only [dite_eq_right hnotfirst, dite_eq_left hfirst2, dite_eq_right hupper']
          rw [targetToInversion.eq_def]
          simp only [Sum.rec, dite_true]
          have hli := lowerIndex_eq s hs (s (first i)) (by rw [pairing_slot]; exact first_slot_value s hs i) rfl
          have hlj := lowerIndex_eq s hs (s (first j)) (by rw [pairing_slot]; exact first_slot_value s hs j) rfl
          dsimp [i, j] at hli hlj
          simp only [hli, hlj]
          exact Prod.ext hsecond.symm hfirst2.symm
      · let j := slotIndex q.val.2
        have hnotfirst2 : ¬ q.val.2 = first (slotIndex q.val.2) := by
          intro h
          have hh := h.symm.trans hsecond2
          have hhval := congrArg Fin.val hh
          simp only [first, second] at hhval
          omega
        have hij := inversion_slot_order s hsecond (Or.inr hsecond2)
        rw [inversionToTarget]
        simp only [dite_eq_right hnotfirst, dite_eq_right hnotfirst2]
        rw [targetToInversion.eq_def]
        simp only [Sum.rec, dite_false]
        have hli := lowerIndex_eq s hs (s (first i)) (by rw [pairing_slot]; exact first_slot_value s hs i) rfl
        have hlj := lowerIndex_eq s hs (s (first j)) (by rw [pairing_slot]; exact first_slot_value s hs j) rfl
        have hb : ¬ ((1 : Fin 2) = 0) := by decide
        simp only [dite_eq_right hb]
        dsimp [i, j] at hli hlj
        simp only [hli, hlj]
        exact Prod.ext hsecond.symm hsecond2.symm
  right_inv := by
    intro z
    classical
    rcases z with q | ⟨q, b⟩
    · let i := lowerIndex s hs q.val.1 (cross_lower hs q).1
      let j := lowerIndex s hs q.val.2 (cross_lower hs q).2.1
      have hi : q.val.1 = s (first i) := lowerIndex_spec s hs q.val.1 (cross_lower hs q).1
      have hj : q.val.2 = s (first j) := lowerIndex_spec s hs q.val.2 (cross_lower hs q).2.1
      have hd := cross_lower hs q
      rw [hi, hj, pairing_slot, pairing_slot] at hd
      have hu : s (second i) < s (second j) := hd.2.2.2.2
      change inversionToTarget s hs (⟨(second i, first j), _⟩ : InvType s) = Sum.inl q
      unfold inversionToTarget
      simp only [slotIndex_second, slotIndex_first, second_ne_first,
        dite_false, dite_true, hu]
      congr 1
      apply Subtype.ext
      exact Prod.ext hi.symm hj.symm
    · let i := lowerIndex s hs q.val.1 (nest_lower hs q).1
      let j := lowerIndex s hs q.val.2 (nest_lower hs q).2.1
      have hi : q.val.1 = s (first i) := lowerIndex_spec s hs q.val.1 (nest_lower hs q).1
      have hj : q.val.2 = s (first j) := lowerIndex_spec s hs q.val.2 (nest_lower hs q).2.1
      have hd := nest_lower hs q
      rw [hi, hj, pairing_slot, pairing_slot] at hd
      have hu : ¬ s (second i) < s (second j) := not_lt_of_gt hd.2.2.2.2
      fin_cases b
      · change inversionToTarget s hs (⟨(second i, first j), _⟩ : InvType s) =
          Sum.inr (q, (0 : Fin 2))
        unfold inversionToTarget
        simp only [slotIndex_second, slotIndex_first, second_ne_first,
          dite_false, dite_true, hu]
        congr 2
        apply Subtype.ext
        exact Prod.ext hi.symm hj.symm
      · change inversionToTarget s hs (⟨(second i, second j), _⟩ : InvType s) =
          Sum.inr (q, (1 : Fin 2))
        unfold inversionToTarget
        simp only [slotIndex_second, second_ne_first, dite_false]
        congr 2
        apply Subtype.ext
        exact Prod.ext hi.symm hj.symm

theorem inversion_card_eq_cross_add_two_nesting_card {n : ℕ}
    (s : Equiv.Perm (Pos n)) (hs : s ∈ normalizedListings n) :
    Fintype.card (InvType s) =
      Fintype.card (CrossType (pairingOfListing s)) +
        2 * Fintype.card (NestType (pairingOfListing s)) := by
  calc
    Fintype.card (InvType s) =
        Fintype.card
          (CrossType (pairingOfListing s) ⊕
            (NestType (pairingOfListing s) × Fin 2)) :=
      Fintype.card_congr (inversionCrossNestEquiv s hs)
    _ = Fintype.card (CrossType (pairingOfListing s)) +
          Fintype.card (NestType (pairingOfListing s)) * Fintype.card (Fin 2) := by
      rw [Fintype.card_sum, Fintype.card_prod]
    _ = Fintype.card (CrossType (pairingOfListing s)) +
          2 * Fintype.card (NestType (pairingOfListing s)) := by
      simp [Nat.mul_comm]

private def orderedPairs (n : ℕ) : Finset (Pair n) :=
  Finset.univ.filter (fun q => q.1 < q.2)

private theorem orderedPairs_filter_inversions {n : ℕ} (s : Equiv.Perm (Pos n)) :
    (orderedPairs n).filter (fun q => s q.2 < s q.1) = inversionPairs s := by
  ext q
  simp [orderedPairs, inversionPairs, and_assoc, and_left_comm, and_comm]

private theorem orderedPairs_filter_membership {n : ℕ} (s : Equiv.Perm (Pos n)) :
    (orderedPairs n).filter (fun q => q ∈ inversionPairs s) = inversionPairs s := by
  calc
    _ = (orderedPairs n).filter (fun q => s q.2 < s q.1) := by
      ext q
      simp [orderedPairs, inversionPairs, and_assoc, and_left_comm, and_comm]
    _ = inversionPairs s := orderedPairs_filter_inversions s

private theorem sign_eq_neg_one_pow_inversion_card {n : ℕ}
    (s : Equiv.Perm (Pos n)) :
    Equiv.Perm.sign s = (-1 : ℤˣ) ^ (inversionPairs s).card := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  rw [← Finset.prod_finset_product' (orderedPairs n) Finset.univ
    (fun i : Pos n => Finset.Ioi i)]
  · have hfactor (q : Pair n) (hq : q ∈ orderedPairs n) :
        (if s q.1 < s q.2 then (1 : ℤˣ) else -1) =
          (if q ∈ inversionPairs s then (-1 : ℤˣ) else 1) := by
      have hne : s q.1 ≠ s q.2 := by
        intro h
        exact (ne_of_lt (Finset.mem_filter.mp hq).2) (s.injective h)
      have hqorder : q.1 < q.2 := (Finset.mem_filter.mp hq).2
      by_cases hlt : s q.1 < s q.2
      · have hle : s q.1 ≤ s q.2 := le_of_lt hlt
        simp [inversionPairs, hqorder, hlt, hle]
      · have hgt : s q.2 < s q.1 :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [orderedPairs, inversionPairs, hqorder, hlt, hgt]
    have hprod :
        (∏ q ∈ orderedPairs n, (if s q.1 < s q.2 then (1 : ℤˣ) else -1)) =
          ∏ q ∈ orderedPairs n, (if q ∈ inversionPairs s then (-1 : ℤˣ) else 1) := by
      apply Finset.prod_congr rfl
      intro q hq
      exact hfactor q hq
    rw [hprod]
    rw [← Finset.prod_filter]
    rw [orderedPairs_filter_membership]
    simp [Finset.prod_const]
  · intro q
    simp [orderedPairs]

noncomputable def lowerEndpointEquiv {n : ℕ}
    (s : Equiv.Perm (Pos n)) (hs : s ∈ normalizedListings n) :
    Fin n ≃ lowerEndpoints (pairingOfListing s) where
  toFun i := ⟨s (first i), by
    have ha : s (first i) < (pairingOfListing s).val (s (first i)) := by
      rw [pairing_slot]
      exact first_slot_value s hs i
    simpa [lowerEndpoints] using ha⟩
  invFun a := lowerIndex s hs a.val (by simpa [lowerEndpoints] using a.property)
  left_inv i := by
    apply lowerIndex_eq s hs (s (first i))
      (by rw [pairing_slot]; exact first_slot_value s hs i)
    rfl
  right_inv a := by
    apply Subtype.ext
    exact (lowerIndex_spec s hs a.val (by simpa [lowerEndpoints] using a.property)).symm

private theorem listing_edge_product_eq {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Pos n) (Pos n) R) (s : Equiv.Perm (Pos n))
    (hs : s ∈ normalizedListings n) :
    (∏ i : Fin n, A (s (first i)) (s (second i))) =
      ∏ a : lowerEndpoints (pairingOfListing s),
        A a.val ((pairingOfListing s).val a.val) := by
  let e := lowerEndpointEquiv s hs
  apply Fintype.prod_equiv e
  intro i
  change A (s (first i)) (s (second i)) =
    A (s (first i)) ((pairingOfListing s).val (s (first i)))
  rw [pairing_slot]

noncomputable def crossingUnit {n : ℕ} (p : P n) : ℤˣ :=
  (-1 : ℤˣ) ^ Fintype.card (CrossType p)

noncomputable def crossingCoefficient {n : ℕ} {R : Type*} [CommRing R]
    (p : P n) : R := ((crossingUnit p : ℤ) : R)

theorem pfaffian_eq_crossing_sum {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Pos n) (Pos n) R) :
    pfaffian A =
      ∑ s ∈ normalizedListings n,
        crossingCoefficient (pairingOfListing s) *
          (∏ a : lowerEndpoints (pairingOfListing s),
            A a.val ((pairingOfListing s).val a.val)) := by
  classical
  unfold pfaffian crossingCoefficient crossingUnit
  apply Finset.sum_congr rfl
  intro s hs
  have hunit :
      Equiv.Perm.sign s =
        (-1 : ℤˣ) ^ Fintype.card (CrossType (pairingOfListing s)) := by
    have hinvcard : Fintype.card (InvType s) = (inversionPairs s).card :=
      Fintype.card_coe _
    rw [sign_eq_neg_one_pow_inversion_card s, ← hinvcard,
      inversion_card_eq_cross_add_two_nesting_card s hs]
    simp [pow_add, pow_mul]
  have hsign :
      (Equiv.Perm.sign s : ℤ) =
        ((((-1 : ℤˣ) ^ Fintype.card (CrossType (pairingOfListing s))) : ℤˣ) : ℤ) :=
    congrArg (fun u : ℤˣ => (u : ℤ)) hunit
  have hprod :
      (∏ i : Fin n,
        A (s ⟨2 * i.val, by omega⟩) (s ⟨2 * i.val + 1, by omega⟩)) =
        ∏ a : lowerEndpoints (pairingOfListing s),
          A a.val ((pairingOfListing s).val a.val) := by
    simpa only [first, second] using listing_edge_product_eq A s hs
  rw [hsign, hprod]

end D5.S0.Certificates.Combinatorics.NormalizedPfaffianCount
