/- GID: D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MatharSameParityRecurrence
   mirror-E: none(waiver:theorem-has-no-separate-numeric-evidence)
   anchors: []
   utility: none
   digest: The integer recurrence for permutations whose first two values have equal parity. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Fintype.BigOperators

/-! # Permutations with equal parity in their first two natural values -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence

open scoped BigOperators

private abbrev GoodPerm (n : ℕ) (h : 2 ≤ n) :=
  {p : Equiv.Perm (Fin n) //
    ((p ⟨0, by omega⟩).val + 1) % 2 = ((p ⟨1, by omega⟩).val + 1) % 2}

/-- The number of permutations of `{1,...,n}` with equal parity in their first two
values. A permutation of `Fin n` represents the natural value `p(i).val + 1`.
The zero values below the source domain are only a totalization. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : 2 ≤ n then (Nat.card (GoodPerm n h) : ℤ) else 0

private abbrev FirstPair (n : ℕ) :=
  {xy : Fin n × Fin n // xy.1 ≠ xy.2 ∧ xy.1.val % 2 = xy.2.val % 2}

private def parityClass (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x.val % 2 = r)

private theorem parityClass_card (n r : ℕ) (hr : r < 2) :
    (parityClass n r).card = n / 2 + if r % 2 < n % 2 then 1 else 0 := by
  have hm : (parityClass n r).map Fin.valEmbedding =
      (Finset.range n).filter (fun x => x % 2 = r) := by
    ext x
    simp only [parityClass, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.isLt, hi⟩
    · rintro ⟨hx, hr⟩
      exact ⟨⟨x, hx⟩, hr, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm,
    ← Nat.count_eq_card_filter_range]
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using
    (Nat.count_modEq_card n (by norm_num : 0 < (2 : ℕ)) r)

private theorem firstPair_card (n : ℕ) :
    Fintype.card (FirstPair n) =
      ((parityClass n 0).card * (parityClass n 0).card - (parityClass n 0).card) +
      ((parityClass n 1).card * (parityClass n 1).card - (parityClass n 1).card) := by
  classical
  let s := (parityClass n 0).offDiag ∪ (parityClass n 1).offDiag
  have hmem (xy : Fin n × Fin n) :
      xy ∈ s ↔ xy.1 ≠ xy.2 ∧ xy.1.val % 2 = xy.2.val % 2 := by
    simp only [s, Finset.mem_union, Finset.mem_offDiag, parityClass,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := Nat.mod_lt xy.1.val (by norm_num : 0 < (2 : ℕ))
    constructor
    · rintro (⟨h0, h1, hne⟩ | ⟨h0, h1, hne⟩)
      · exact ⟨hne, h0.trans h1.symm⟩
      · exact ⟨hne, h0.trans h1.symm⟩
    · rintro ⟨hne, he⟩
      by_cases h0 : xy.1.val % 2 = 0
      · exact Or.inl ⟨h0, by omega, hne⟩
      · exact Or.inr ⟨by omega, by omega, hne⟩
  have hd : Disjoint (parityClass n 0).offDiag (parityClass n 1).offDiag := by
    apply Finset.disjoint_left.mpr
    intro xy hx hy
    have h0 := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hx).1).2
    have h1 := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hy).1).2
    omega
  rw [Fintype.card_of_subtype s hmem, Finset.card_union_of_disjoint hd,
    Finset.offDiag_card, Finset.offDiag_card]

private abbrev Completion (n : ℕ) (h : 2 ≤ n) (xy : FirstPair n) :=
  {p : Equiv.Perm (Fin n) //
    p ⟨0, by omega⟩ = xy.val.1 ∧ p ⟨1, by omega⟩ = xy.val.2}

private theorem completion_card (n : ℕ) (h : 2 ≤ n) (xy : FirstPair n) :
    Nat.card (Completion n h xy) = Nat.factorial (n - 2) := by
  classical
  let d : Fin 2 → Fin n := fun i => ⟨i.val, by omega⟩
  let l : Fin 2 → Fin n := ![xy.val.1, xy.val.2]
  have hd : Function.Injective d := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)
  have hl : Function.Injective l := by
    have hne := xy.property.1
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [l]
  have hp (p : Equiv.Perm (Fin n)) :
      (p ⟨0, by omega⟩ = xy.val.1 ∧ p ⟨1, by omega⟩ = xy.val.2) ↔
        ∀ i, p (d i) = l i := by
    constructor
    · intro hh i
      fin_cases i
      · exact hh.1
      · exact hh.2
    · intro hh
      exact ⟨hh 0, hh 1⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
  simpa using
    (D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting.nat_card_equiv_constraints
      d l hd hl rfl)

/-- Reading the first pair and retaining its permutation is an exact decomposition
of the source sample space into disjoint completion fibers. -/
private def sourceEquivCompletions (n : ℕ) (h : 2 ≤ n) :
    GoodPerm n h ≃ Σ xy : FirstPair n, Completion n h xy where
  toFun p :=
    ⟨⟨(p.val ⟨0, by omega⟩, p.val ⟨1, by omega⟩), by
      constructor
      · change p.val ⟨0, by omega⟩ ≠ p.val ⟨1, by omega⟩
        intro he
        have hh := congrArg (fun x : Fin n => x.val) (p.val.injective he)
        norm_num at hh
      · have hp := p.property
        change (p.val ⟨0, by omega⟩).val % 2 = (p.val ⟨1, by omega⟩).val % 2
        omega⟩, ⟨p.val, rfl, rfl⟩⟩
  invFun q := ⟨q.2.val, by
    have h0 := congrArg Fin.val q.2.property.1
    have h1 := congrArg Fin.val q.2.property.2
    have hp := q.1.property.2
    omega⟩
  left_inv p := by rfl
  right_inv q := by
    apply Sigma.ext (Subtype.ext (Prod.ext q.2.property.1 q.2.property.2))
    refine (Subtype.heq_iff_coe_eq ?_).2 rfl
    intro p
    change (p ⟨0, by omega⟩ = q.2.val ⟨0, by omega⟩ ∧
      p ⟨1, by omega⟩ = q.2.val ⟨1, by omega⟩) ↔
      (p ⟨0, by omega⟩ = q.1.val.1 ∧ p ⟨1, by omega⟩ = q.1.val.2)
    rw [q.2.property.1, q.2.property.2]

private theorem source_count (n : ℕ) (h : 2 ≤ n) :
    a n = (Fintype.card (FirstPair n) : ℤ) * (Nat.factorial (n - 2) : ℤ) := by
  classical
  rw [a, dite_eq_left h, Nat.card_congr (sourceEquivCompletions n h), Nat.card_sigma]
  simp_rw [completion_card n h]
  simp

private theorem a_even (k : ℕ) :
    a (2 * k + 2) = 2 * (k + 1 : ℤ) * k * (Nat.factorial (2 * k) : ℤ) := by
  have hp : Fintype.card (FirstPair (2 * k + 2)) = 2 * (k + 1) * k := by
    rw [firstPair_card, parityClass_card _ 0 (by norm_num),
      parityClass_card _ 1 (by norm_num)]
    have hd : (2 * k + 2) / 2 = k + 1 := by omega
    have hm : (2 * k + 2) % 2 = 0 := by omega
    have hs : (k + 1) * (k + 1) - (k + 1) = (k + 1) * k := by
      have he : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      omega
    simp [hd, hm, hs] <;> ring
  rw [source_count _ (by omega), hp, show 2 * k + 2 - 2 = 2 * k by omega]
  push_cast
  ring

private theorem a_odd (k : ℕ) :
    a (2 * k + 3) = 2 * (k + 1 : ℤ) ^ 2 * (Nat.factorial (2 * k + 1) : ℤ) := by
  have hp : Fintype.card (FirstPair (2 * k + 3)) = 2 * (k + 1) ^ 2 := by
    rw [firstPair_card, parityClass_card _ 0 (by norm_num),
      parityClass_card _ 1 (by norm_num)]
    have hd : (2 * k + 3) / 2 = k + 1 := by omega
    have hm : (2 * k + 3) % 2 = 1 := by omega
    have hs (j : ℕ) : (j + 1) * (j + 1) - (j + 1) = (j + 1) * j := by
      have he : (j + 1) * (j + 1) = (j + 1) * j + (j + 1) := by ring
      omega
    simp [hd, hm, hs] <;> ring
  rw [source_count _ (by omega), hp, show 2 * k + 3 - 2 = 2 * k + 1 by omega]
  push_cast
  ring

/-- Mathar's first conjectural FORMULA for OEIS A152661, with the source
permutation count and signed integer coefficients, at every index in its domain. -/
theorem result (n : ℕ) (hn : 4 ≤ n) :
    (3 - (n : ℤ)) * a n + 2 * ((n : ℤ) - 2) * a (n - 1) +
      ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 2) = 0 := by
  by_cases hpar : n % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 4 := ⟨(n - 4) / 2, by omega⟩
    have htop := a_even (k + 1)
    have hi : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
    have hf : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [hi, hf] at htop
    rw [show 2 * k + 4 - 1 = 2 * k + 3 by omega,
      show 2 * k + 4 - 2 = 2 * k + 2 by omega, htop, a_odd k, a_even k]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 5 := ⟨(n - 5) / 2, by omega⟩
    have htop := a_odd (k + 1)
    have hmid := a_even (k + 1)
    have hi : 2 * (k + 1) + 3 = 2 * k + 5 := by ring
    have hj : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
    have hf : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    have hg : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [hi, hf] at htop
    rw [hj, hg] at hmid
    rw [show 2 * k + 5 - 1 = 2 * k + 4 by omega,
      show 2 * k + 5 - 2 = 2 * k + 3 by omega, htop, hmid, a_odd k]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring

end D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence
