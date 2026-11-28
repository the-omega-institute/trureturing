import Mathlib.InformationTheory.Hamming

/-! In the seven-axis contact graph whose complement is a triangle, the three
independent axes and two inactive axes form a five-dimensional fibre. On a fixed
parity, a mixed fibre can only have cross distances four. Its occupancy bound
follows from the distance-`n - 1` graph of a binary cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFibreCapacity

open Finset

variable {n : ℕ}

/-- The binary word obtained by complementing every coordinate except `i`. -/
private def complementExcept (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then x j else !x j

private theorem agreement_singleton {x y : Fin n → Bool} (h : hammingDist x y + 1 = n) :
    ∃ i, (univ.filter fun j => x j = y j) = {i} := by
  apply card_eq_one.mp
  have hsplit := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n))) (fun j => x j ≠ y j)
  rw [← hammingDist, card_univ, Fintype.card_fin] at hsplit
  simpa only [not_not] using Nat.add_left_cancel (hsplit.trans h.symm)

private theorem complementExcept_of_agree {x y : Fin n → Bool}
    (h : hammingDist x y + 1 = n) {i : Fin n} (hi : x i = y i) :
    y = complementExcept x i := by
  obtain ⟨k, hk⟩ := agreement_singleton h
  have hik : i = k := by
    simpa [hk] using (mem_filter.mpr ⟨mem_univ i, hi⟩ :
      i ∈ (univ.filter fun j => x j = y j))
  subst k
  funext j
  by_cases hj : j = i
  · subst j
    simpa [complementExcept] using hi.symm
  · have hne : y j ≠ x j := by
      intro he
      have hmem : j ∈ (univ.filter fun l => x l = y l) :=
        mem_filter.mpr ⟨mem_univ j, he.symm⟩
      exact hj (by simpa [hk] using hmem)
    simpa [complementExcept, hj] using Bool.eq_not_of_ne hne

open Classical in
private theorem card_le_of_distances {x : Fin n → Bool} {S : Finset (Fin n → Bool)}
    (h : ∀ z ∈ S, hammingDist x z + 1 = n) : S.card ≤ n := by
  have hsub : S ⊆ (univ : Finset (Fin n)).image (complementExcept x) := by
    intro z hz
    obtain ⟨i, hi⟩ := agreement_singleton (h z hz)
    have hmem : i ∈ (univ.filter fun j => x j = z j) := by simp [hi]
    exact mem_image.mpr ⟨i, mem_univ i,
      (complementExcept_of_agree (h z hz) (mem_filter.mp hmem).2).symm⟩
  exact (card_le_card hsub).trans (by simpa using
    (card_image_le (s := (univ : Finset (Fin n))) (f := complementExcept x)))

open Classical in
private theorem card_le_two_of_common_distances {x y : Fin n → Bool} (hne : x ≠ y)
    {S : Finset (Fin n → Bool)} (hx : ∀ z ∈ S, hammingDist x z + 1 = n)
    (hy : ∀ z ∈ S, hammingDist y z + 1 = n) : S.card ≤ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hsub : S ⊆ {complementExcept x i, complementExcept y i} := by
    intro z hz
    by_cases hxi : x i = z i
    · simp [complementExcept_of_agree (hx z hz) hxi]
    · have hyi : y i = z i := by
        cases hxbit : x i <;> cases hybit : y i <;> cases hzbit : z i <;>
          simp_all
      simp [complementExcept_of_agree (hy z hz) hyi]
  refine (card_le_card hsub).trans ?_
  by_cases heq : complementExcept x i = complementExcept y i
  · simp [heq]
  · rw [card_pair heq]

open Classical in
/-- For two nonempty families at cross distance one less than the dimension,
one side has size one and the other has size at most `n`, or both sides have
size two. This bounds a mixed five-dimensional contact fibre by six. -/
theorem cross_distance_four_card_bound (C D : Finset (Fin 5 → Bool))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hdist : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 4) :
    C.card ≤ 5 ∧ D.card ≤ 5 ∧ C.card + D.card ≤ 6 ∧
      (1 < C.card → D.card ≤ 2) ∧ (1 < D.card → C.card ≤ 2) := by
  obtain ⟨x, hx⟩ := hC
  obtain ⟨y, hy⟩ := hD
  have hCD (u : Fin 5 → Bool) (hu : u ∈ C) (v : Fin 5 → Bool) (hv : v ∈ D) :
      hammingDist u v + 1 = 5 := by rw [hdist u hu v hv]
  have hleft := card_le_of_distances (fun u hu => by
    rw [hammingDist_comm]
    exact hCD u hu y hy)
  have hright := card_le_of_distances (fun v hv => hCD x hx v hv)
  have hpairRight (h : 1 < C.card) : D.card ≤ 2 := by
    obtain ⟨a, b, ha, hb, hne⟩ := one_lt_card_iff.mp h
    exact card_le_two_of_common_distances hne (hCD a ha) (hCD b hb)
  have hpairLeft (h : 1 < D.card) : C.card ≤ 2 := by
    obtain ⟨a, b, ha, hb, hne⟩ := one_lt_card_iff.mp h
    exact card_le_two_of_common_distances hne
      (fun u hu => by rw [hammingDist_comm]; exact hCD u hu a ha)
      (fun u hu => by rw [hammingDist_comm]; exact hCD u hu b hb)
  refine ⟨hleft, hright, ?_, hpairRight, hpairLeft⟩
  by_cases hClarge : 1 < C.card
  · by_cases hDlarge : 1 < D.card
    · have := hpairRight hClarge
      have := hpairLeft hDlarge
      omega
    · omega
  · omega

#print axioms cross_distance_four_card_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFibreCapacity
