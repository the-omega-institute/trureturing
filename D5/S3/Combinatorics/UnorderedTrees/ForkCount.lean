/- GID: D5/S3/Combinatorics/UnorderedTrees/ForkCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/ForkCount
   mirror-E: none(waiver:unordered-tree-fork-count)
   anchors: [mathlib/module/Mathlib.Data.Sym.NatCard]
   utility: none
   digest: Bounded binomial sums count the two fork decoration families of each size. -/

import D5.S3.Combinatorics.UnorderedTrees.ForkDecoration
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard

/-! Counting the two fork types by weighted weak compositions. -/

namespace D5.S3.Combinatorics.UnorderedTrees.ForkCount

open ParentTree ForkDecoration
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- A weak composition with an explicit base weight. -/
abbrev Slots (n base k : ℕ) := {f : Fin k → ℕ // base + ∑ i, f i = n}

private def slotEquiv (n base k : ℕ) (h : base ≤ n) :
    Sym (Fin k) (n - base) ≃ Slots n base k :=
  (Sym.equivNatSumOfFintype (Fin k) _).trans
    ((Equiv.refl _).subtypeEquiv (by
      intro f
      change ((∑ i, f i) = n - base) ↔ base + (∑ i, f i) = n
      omega))

private instance (n base k : ℕ) : Finite (Slots n base k) := by
  by_cases h : base ≤ n
  · exact Finite.of_equiv _ (slotEquiv n base k h)
  · let _ : IsEmpty (Slots n base k) := ⟨fun ⟨_, hf⟩ => h (by omega)⟩
    infer_instance

private instance (n base k : ℕ) : Fintype (Slots n base k) := Fintype.ofFinite _

private theorem card_slots (n base j : ℕ) :
    Nat.card (Slots n base (j + 1)) = if base ≤ n then (j + (n - base)).choose j else 0 := by
  by_cases h : base ≤ n
  · rw [ite_eq_left h, ← Nat.card_congr (slotEquiv n base (j + 1) h), Sym.natCard_sym_eq_choose,
      Nat.card_fin, show j + 1 + (n - base) - 1 = j + (n - base) by omega]
    exact Nat.choose_symm_add.symm
  · rw [ite_eq_right h]
    have : IsEmpty (Slots n base (j + 1)) := ⟨fun ⟨_, hf⟩ => h (by omega)⟩
    exact Nat.card_of_isEmpty

/-- Equal arms use the smaller tip offset `m` and one slot for the difference. -/
abbrev Equal (n : ℕ) :=
  Σ b : Fin (n + 1), Σ m : Fin (n + 1), Slots n (b.val + 5 + 2 * m.val) (b.val + 2)

/-- Unequal arms use both tip offsets as independent slots. -/
abbrev Unequal (n : ℕ) :=
  Σ b : Fin (n + 1), Σ c : Fin (n + 1),
    {_f : Slots n (b.val + c.val + 5) (b.val + c.val + 3) // 0 < c.val}

private theorem sum_snoc {k : ℕ} (f : Fin k → ℕ) (x : ℕ) :
    (∑ i, Fin.snoc f x i) = (∑ i, f i) + x := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

private def decode (n : ℕ) : Equal n ⊕ Unequal n → Weighted n
  | .inl ⟨b, m, ⟨f, hf⟩⟩ =>
    ⟨⟨b.val, 0, ⟨Fin.init f, m.val, m.val + f (Fin.last (b.val + 1)),
      fun _ => Nat.le_add_right _ _⟩⟩, by
        change b.val + 5 + (∑ i, Fin.init f i) + m.val +
          (m.val + f (Fin.last (b.val + 1))) = n
        rw [Fin.sum_univ_castSucc] at hf
        exact by dsimp [Fin.init] at *; omega⟩
  | .inr ⟨b, c, ⟨⟨f, hf⟩, hc⟩⟩ =>
    ⟨⟨b.val, c.val, ⟨Fin.init (Fin.init f),
      Fin.init f (Fin.last (b.val + c.val + 1)), f (Fin.last (b.val + c.val + 2)),
      fun h => (Nat.ne_of_gt hc h).elim⟩⟩, by
        change b.val + c.val + 5 + (∑ i, Fin.init (Fin.init f) i) +
          Fin.init f (Fin.last (b.val + c.val + 1)) + f (Fin.last (b.val + c.val + 2)) = n
        rw [Fin.sum_univ_castSucc (n := b.val + c.val + 2)] at hf
        change b.val + c.val + 5 + ((∑ i, Fin.init f i) + _) = n at hf
        rw [Fin.sum_univ_castSucc (n := b.val + c.val + 1)] at hf
        exact by dsimp [Fin.init] at *; omega⟩

private def encode (n : ℕ) (d : Weighted n) : Equal n ⊕ Unequal n := by
  obtain ⟨⟨b, c, r⟩, hd⟩ := d
  change b + c + 5 + (∑ i, r.spine i) + r.short + r.long = n at hd
  by_cases hc : c = 0
  · subst c
    simp only [Nat.add_zero] at hd
    refine .inl ⟨⟨b, by omega⟩, ⟨r.short, by omega⟩,
      ⟨Fin.snoc r.spine (r.long - r.short), ?_⟩⟩
    change b + 5 + 2 * r.short + (∑ i, Fin.snoc r.spine (r.long - r.short) i) = n
    rw [sum_snoc]
    have hs := r.sorted rfl
    omega
  · refine .inr ⟨⟨b, by omega⟩, ⟨c, by omega⟩,
      ⟨⟨Fin.snoc (Fin.snoc r.spine r.short) r.long, ?_⟩, Nat.pos_of_ne_zero hc⟩⟩
    change b + c + 5 + (∑ i, Fin.snoc (Fin.snoc r.spine r.short) r.long i) = n
    rw [sum_snoc, sum_snoc]
    omega

/-- Equal arms use the unique representation `(m,m+d)` of their sorted offsets. -/
def weightSplit (n : ℕ) : Weighted n ≃ Equal n ⊕ Unequal n where
  toFun := encode n
  invFun := decode n
  left_inv := by
    rintro ⟨⟨b, c, r⟩, hd⟩
    by_cases hc : c = 0
    · subst c
      apply Subtype.ext
      simp [id, encode, decode, Nat.add_sub_of_le (r.sorted rfl)]
    · apply Subtype.ext
      simp [id, encode, decode, hc]
  right_inv := by
    rintro (⟨b, m, ⟨f, hf⟩⟩ | ⟨b, c, ⟨⟨f, hf⟩, hc⟩⟩)
    · simp [id, decode, encode]
      rfl
    · simp [id, decode, encode, Nat.ne_of_gt hc]
      rfl

private theorem sum_fin_pair (n : ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ b : Fin n, ∑ c : Fin n, f b c) = ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n, f b c := by
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => ∑ c : Fin n, f b c)]
  exact Finset.sum_congr rfl fun b _ => Fin.sum_univ_eq_sum_range (f b) n

private theorem card_equal (n : ℕ) :
    Nat.card (Equal n) = ∑ b ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
      if b + 5 + 2 * m ≤ n then (n - 4 - 2 * m).choose (b + 1) else 0 := by
  unfold Equal
  simp only [Nat.card_sigma]
  rw [← sum_fin_pair]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro m _
  rw [card_slots]
  split
  · rename_i h
    congr 1
    omega
  · rfl

private theorem card_unequal_pair (n b c : ℕ) :
    Nat.card {_f : Slots n (b + c + 5) (b + c + 3) // 0 < c} =
      if 0 < c ∧ b + c + 5 ≤ n then (n - 3).choose (b + c + 2) else 0 := by
  by_cases hc : 0 < c
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => hc)), card_slots]
    simp only [hc, true_and]
    split
    · rename_i h
      congr 1
      omega
    · rfl
  · simp only [hc, false_and, ite_false]
    have : IsEmpty {_f : Slots n (b + c + 5) (b + c + 3) // 0 < c} :=
      ⟨fun x => hc x.property⟩
    exact Nat.card_of_isEmpty

private theorem card_unequal (n : ℕ) :
    Nat.card (Unequal n) = ∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1),
      if 0 < c ∧ b + c + 5 ≤ n then (n - 3).choose (b + c + 2) else 0 := by
  unfold Unequal
  simp only [Nat.card_sigma, card_unequal_pair]
  exact sum_fin_pair (n + 1) (fun b c =>
    if 0 < c ∧ b + c + 5 ≤ n then (n - 3).choose (b + c + 2) else 0)

private theorem regroup_unequal (n : ℕ) :
    (∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1),
      if 0 < c ∧ b + c + 5 ≤ n then (n - 3).choose (b + c + 2) else 0) =
      ∑ v ∈ Finset.range (n - 5), (v + 1) * (n - 3).choose (v + 3) := by
  let pairs := ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p : ℕ × ℕ => 0 < p.2 ∧ p.1 + p.2 + 5 ≤ n)
  let diagonals := (Finset.range (n - 5)).sigma (fun v => Finset.range (v + 1))
  have reindex :
      (∑ p ∈ pairs, (n - 3).choose (p.1 + p.2 + 2)) =
        ∑ q ∈ diagonals, (n - 3).choose (q.1 + 3) := by
    apply Finset.sum_nbij' (fun p => ⟨p.1 + p.2 - 1, p.1⟩)
      (fun q => (q.2, q.1 + 1 - q.2))
    · intro p hp
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [diagonals, Finset.mem_sigma, Finset.mem_range]
      omega
    · intro q hq
      simp only [diagonals, Finset.mem_sigma, Finset.mem_range] at hq
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro p hp
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      apply Prod.ext
      · rfl
      · dsimp
        omega
    · intro q hq
      simp only [diagonals, Finset.mem_sigma, Finset.mem_range] at hq
      suffices h : q.2 + (q.1 + 1 - q.2) - 1 = q.1 by
        cases q
        simp_all
      omega
    · intro p hp
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      congr 1
      dsimp
      omega
  calc
    _ = ∑ p ∈ pairs, (n - 3).choose (p.1 + p.2 + 2) := by
      simp only [pairs, Finset.sum_filter, Finset.sum_product]
    _ = ∑ q ∈ diagonals, (n - 3).choose (q.1 + 3) := reindex
    _ = _ := by simp [diagonals, Finset.sum_sigma]

/-- The all-size binomial count from the original isomorphism classes. -/
theorem count_by_arms (n : ℕ) :
    a n =
      (∑ b ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        if b + 5 + 2 * m ≤ n then (n - 4 - 2 * m).choose (b + 1) else 0) +
      (∑ v ∈ Finset.range (n - 5), (v + 1) * (n - 3).choose (v + 3)) := by
  have : Finite (Equal n) := by unfold Equal; infer_instance
  have : Finite (Unequal n) := by unfold Unequal; infer_instance
  rw [← card_weighted, Nat.card_congr (weightSplit n), Nat.card_sum, card_equal, card_unequal,
    regroup_unequal]

#print axioms weightSplit
#print axioms count_by_arms

end

end D5.S3.Combinatorics.UnorderedTrees.ForkCount
