/- GID: D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian
   generality: G
   mirror-B: D5/B/S0/Certificates/Combinatorics/ForcedLastPairPfaffian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A zero penultimate upper column forces a final pair in the normalized Pfaffian. -/

import D5.S0.Certificates.Combinatorics.NormalizedPfaffian

/-! Forced final-pair factorization over a commutative ring. -/

set_option warningAsError true
set_option autoImplicit false

open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing (first second index_cases)

open D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation (normalizedListings pfaffian)

namespace D5.S0.Certificates.Combinatorics.NormalizedPfaffian

def embed {n : ℕ} (i : Fin (2 * n)) : Fin (2 * (n + 1)) :=
  ⟨i.val, by omega⟩

def last0 (n : ℕ) : Fin (2 * (n + 1)) := ⟨2 * n, by omega⟩
def last1 (n : ℕ) : Fin (2 * (n + 1)) := ⟨2 * n + 1, by omega⟩

private def embedEquiv (n : ℕ) :
    Fin (2 * n) ≃ {x : Fin (2 * (n + 1)) // x.val < 2 * n} where
  toFun i := ⟨embed i, i.isLt⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def extendListing {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm (Fin (2 * (n + 1))) :=
  s.extendDomain (embedEquiv n)

private theorem extendListing_old {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) (i : Fin (2 * n)) :
    extendListing s (embed i) = embed (s i) :=
  Equiv.Perm.extendDomain_apply_subtype s (embedEquiv n) (b := embed i) i.isLt

private theorem extendListing_last0 {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    extendListing s (last0 n) = last0 n :=
  Equiv.Perm.extendDomain_apply_not_subtype s (embedEquiv n) (Nat.lt_irrefl _)

private theorem extendListing_last1 {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    extendListing s (last1 n) = last1 n :=
  Equiv.Perm.extendDomain_apply_not_subtype s (embedEquiv n) (Nat.not_lt_of_ge (Nat.le_succ _))

private theorem sign_extendListing {n : ℕ} (s : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm.sign (extendListing s) = Equiv.Perm.sign s :=
  Equiv.Perm.sign_extendDomain s (embedEquiv n)

private theorem first_castSucc {n : ℕ} (i : Fin n) :
    first i.castSucc = embed (first i) := rfl

private theorem second_castSucc {n : ℕ} (i : Fin n) :
    second i.castSucc = embed (second i) := rfl

private theorem first_last (n : ℕ) : first (Fin.last n) = last0 n := rfl
private theorem second_last (n : ℕ) : second (Fin.last n) = last1 n := rfl

private theorem embed_lt_last0 {n : ℕ} (i : Fin (2 * n)) : embed i < last0 n :=
  i.isLt

private theorem mem_normalizedListings {n : ℕ} {s : Equiv.Perm (Fin (2 * n))} :
    s ∈ normalizedListings n ↔
      (∀ i : Fin n, s (first i) < s (second i)) ∧
      ∀ i j : Fin n, i < j → s (first i) < s (first j) := by
  simp only [normalizedListings, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

private theorem extendListing_normalized {n : ℕ} {s : Equiv.Perm (Fin (2 * n))}
    (hs : s ∈ normalizedListings n) :
    extendListing s ∈ normalizedListings (n + 1) := by
  obtain ⟨hpair, horder⟩ := mem_normalizedListings.mp hs
  apply mem_normalizedListings.mpr
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [first_last, second_last, extendListing_last0, extendListing_last1]
      exact Nat.lt_succ_self _
    · rw [first_castSucc, second_castSucc, extendListing_old, extendListing_old]
      exact hpair j
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro j hij
      exact (not_lt_of_ge (Fin.le_last j) hij).elim
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        rw [first_castSucc, first_last, extendListing_old, extendListing_last0]
        exact embed_lt_last0 _
      · intro hij
        rw [first_castSucc, first_castSucc, extendListing_old, extendListing_old]
        exact horder i j hij

private def listingTerm {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (s : Equiv.Perm (Fin (2 * n))) : R :=
  ((Equiv.Perm.sign s : ℤ) : R) * ∏ i : Fin n, A (s (first i)) (s (second i))

private theorem listingTerm_eq_zero_without_last_pair {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
    (hzero : ∀ i : Fin (2 * n), A (embed i) (last0 n) = 0)
    {s : Equiv.Perm (Fin (2 * (n + 1)))} (hs : s ∈ normalizedListings (n + 1))
    (hfix : ¬ (s (last0 n) = last0 n ∧ s (last1 n) = last1 n)) :
    listingTerm A s = 0 := by
  obtain ⟨hpair, horder⟩ := mem_normalizedListings.mp hs
  obtain ⟨i, hi | hi⟩ := index_cases (s.symm (last0 n))
  · have ha : s (first i) = last0 n :=
      (congrArg s hi).symm.trans (s.apply_symm_apply _)
    have hb : s (second i) = last1 n := by
      have h := hpair i
      rw [ha] at h
      change 2 * n < (s (second i)).val at h
      apply Fin.ext
      change (s (second i)).val = 2 * n + 1
      omega
    have hlast : i = Fin.last n := by
      apply le_antisymm (Fin.le_last i)
      by_contra! h
      have h0 := horder i (Fin.last n) h
      have h1 := hpair (Fin.last n)
      rw [ha] at h0
      have hh := h0.trans h1
      change 2 * n < (s (second (Fin.last n))).val at hh
      have he : s (second (Fin.last n)) = last1 n := by
        apply Fin.ext
        change (s (second (Fin.last n))).val = 2 * n + 1
        omega
      have hi' := congrArg Fin.val (s.injective (hb.trans he.symm))
      change 2 * i.val + 1 = 2 * n + 1 at hi'
      change i.val < n at h
      omega
    subst i
    exact (hfix ⟨ha, hb⟩).elim
  · have ha : s (second i) = last0 n :=
      (congrArg s hi).symm.trans (s.apply_symm_apply _)
    have hb := hpair i
    rw [ha] at hb
    change (s (first i)).val < 2 * n at hb
    have hfactor : A (s (first i)) (s (second i)) = 0 := by
      rw [ha]
      exact hzero ⟨_, hb⟩
    unfold listingTerm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hfactor, mul_zero]

private theorem index_split {n : ℕ} (x : Fin (2 * (n + 1))) :
    (∃ i : Fin (2 * n), x = embed i) ∨ x = last0 n ∨ x = last1 n := by
  by_cases hx : x.val < 2 * n
  · exact Or.inl ⟨⟨x.val, hx⟩, rfl⟩
  · right
    have h : x.val = 2 * n ∨ x.val = 2 * n + 1 := by omega
    exact h.imp Fin.ext Fin.ext

private theorem preserves_prefix {n : ℕ} (s : Equiv.Perm (Fin (2 * (n + 1))))
    (h0 : s (last0 n) = last0 n) (h1 : s (last1 n) = last1 n)
    (x : Fin (2 * (n + 1))) :
    (s x).val < 2 * n ↔ x.val < 2 * n := by
  constructor
  · intro hx
    rcases index_split x with ⟨i, rfl⟩ | rfl | rfl
    · exact i.isLt
    · rw [h0] at hx
      exact (Nat.lt_irrefl _ hx).elim
    · rw [h1] at hx
      exact (Nat.not_lt_of_ge (Nat.le_succ _) hx).elim
  · intro hx
    rcases index_split (s x) with ⟨i, hi⟩ | hi | hi
    · rw [hi]
      exact i.isLt
    · have he := s.injective (hi.trans h0.symm)
      rw [he] at hx
      exact (Nat.lt_irrefl _ hx).elim
    · have he := s.injective (hi.trans h1.symm)
      rw [he] at hx
      exact (Nat.not_lt_of_ge (Nat.le_succ _) hx).elim

private noncomputable def extendListingEmbedding (n : ℕ) :
    Equiv.Perm (Fin (2 * n)) ↪ Equiv.Perm (Fin (2 * (n + 1))) where
  toFun := extendListing
  inj' := by
    intro s t h
    ext i
    have hi := congrArg (fun u : Equiv.Perm (Fin (2 * (n + 1))) => u (embed i)) h
    rw [extendListing_old, extendListing_old] at hi
    have hv := congrArg (fun x : Fin (2 * (n + 1)) => x.val) hi
    exact hv

private theorem mem_map_extendListing_iff {n : ℕ}
    (s : Equiv.Perm (Fin (2 * (n + 1)))) :
    s ∈ (normalizedListings n).map (extendListingEmbedding n) ↔
      s ∈ normalizedListings (n + 1) ∧ s (last0 n) = last0 n ∧ s (last1 n) = last1 n := by
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    exact ⟨extendListing_normalized ht, extendListing_last0 t, extendListing_last1 t⟩
  · rintro ⟨hs, h0, h1⟩
    obtain ⟨hpair, horder⟩ := mem_normalizedListings.mp hs
    let t := (embedEquiv n).permCongr.symm (s.subtypePerm (preserves_prefix s h0 h1))
    have ht (i : Fin (2 * n)) : embed (t i) = s (embed i) := rfl
    refine Finset.mem_map.mpr ⟨t, mem_normalizedListings.mpr ⟨?_, ?_⟩, ?_⟩
    · intro i
      have hi := hpair i.castSucc
      rw [first_castSucc, second_castSucc, ← ht, ← ht] at hi
      exact hi
    · intro i j hij
      have hi := horder i.castSucc j.castSucc hij
      rw [first_castSucc, first_castSucc, ← ht, ← ht] at hi
      exact hi
    · change extendListing t = s
      apply Equiv.ext
      intro x
      rcases index_split x with ⟨i, rfl⟩ | rfl | rfl
      · rw [extendListing_old, ht]
      · rw [extendListing_last0, h0]
      · rw [extendListing_last1, h1]

private theorem listingTerm_extend {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
    (s : Equiv.Perm (Fin (2 * n))) :
    listingTerm A (extendListing s) =
      listingTerm (A.submatrix embed embed) s * A (last0 n) (last1 n) := by
  unfold listingTerm
  rw [sign_extendListing, Fin.prod_univ_castSucc]
  simp only [first_last, second_last, extendListing_last0, extendListing_last1,
    first_castSucc, second_castSucc, extendListing_old, Matrix.submatrix_apply, mul_assoc]

/-- A zero penultimate column above the diagonal forces the penultimate and last
indices to pair, contributing their entry with positive sign. -/
theorem pfaffian_forced_last_pair {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
    (hzero : ∀ i : Fin (2 * n), A (embed i) (last0 n) = 0) :
    pfaffian A = pfaffian (A.submatrix embed embed) * A (last0 n) (last1 n) := by
  change (∑ s ∈ normalizedListings (n + 1), listingTerm A s) =
    (∑ s ∈ normalizedListings n, listingTerm (A.submatrix embed embed) s) *
      A (last0 n) (last1 n)
  calc
    _ = ∑ s ∈ (normalizedListings n).map (extendListingEmbedding n), listingTerm A s := by
      symm
      apply Finset.sum_subset
      · intro s hs
        exact ((mem_map_extendListing_iff s).mp hs).1
      · intro s hs hnot
        exact listingTerm_eq_zero_without_last_pair A hzero hs
          (fun hfix => hnot ((mem_map_extendListing_iff s).mpr ⟨hs, hfix⟩))
    _ = _ := by
      rw [Finset.sum_map, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      exact listingTerm_extend A s

end D5.S0.Certificates.Combinatorics.NormalizedPfaffian
