/- GID: D5/S3/Arith/GranvikRedhefferSupport
   generality: I
   mirror-B: D5/B/S3/Arith/GranvikRedhefferSupport
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=refutes=gid:D5/S3/Arith/GranvikRedhefferSupport.claim; result=D5/S3/Arith/GranvikRedhefferSupport.result; claim=D5/S3/Arith/GranvikRedhefferSupport.claim
   digest: The divisor-chain support count refutes Granvik's conjectured Redheffer support values. -/

import Mathlib.NumberTheory.Divisors
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

/-! # Divisor-chain support of the modified Redheffer matrix -/

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.GranvikRedhefferSupport

/-- One-based row and column indices. -/
abbrev Index (n : ℕ) := ↥(Icc 1 n)

/-- The Möbius variant of the Redheffer matrix, with its last diagonal entry removed. -/
def B (n : ℕ) : Matrix (Index n) (Index n) ℕ := fun i j =>
  if (j.1 = 1 ∨ i.1 ∣ j.1) ∧ ¬(i.1 = n ∧ j.1 = n) then 1 else 0

/-- Positions occurring in a nonzero permutation term of the determinant. -/
noncomputable def contributingPositions (n : ℕ) : Finset (Index n × Index n) := by
  classical
  exact univ.filter fun p => ∃ σ : Equiv.Perm (Index n),
    σ p.1 = p.2 ∧ ∀ k, B n k (σ k) = 1

/-- The size of the union of supports of all nonzero determinant terms. -/
noncomputable def a (n : ℕ) : ℕ := (contributingPositions n).card

/-- Granvik's twenty conjectured values, in their published order. -/
def claim : Prop :=
  a 11 = 11 ∧ a 12 = 23 ∧ a 13 = 13 ∧ a 14 = 18 ∧ a 15 = 19 ∧
  a 16 = 25 ∧ a 17 = 17 ∧ a 18 = 29 ∧ a 19 = 19 ∧ a 20 = 30 ∧
  a 21 = 26 ∧ a 22 = 26 ∧ a 23 = 23 ∧ a 24 = 45 ∧ a 25 = 27 ∧
  a 26 = 30 ∧ a 27 = 32 ∧ a 28 = 39 ∧ a 29 = 29 ∧ a 30 = 48

private lemma entry_one {n : ℕ} (i j : Index n) :
    B n i j = 1 ↔ (j.1 = 1 ∨ i.1 ∣ j.1) ∧ ¬(i.1 = n ∧ j.1 = n) := by
  simp [B]

private lemma first_column {n : ℕ} (σ : Equiv.Perm (Index n))
    (hσ : ∀ k, B n k (σ k) = 1) (i : Index n) (hi : (σ i).1 = 1) :
    i.1 = n := by
  let last : Index n := ⟨n, by simp only [mem_Icc]; have := (mem_Icc.mp i.2); omega⟩
  have himage : (σ last).1 = 1 := by
    have hentry := (entry_one last (σ last)).mp (hσ last)
    rcases hentry.1 with h1 | hd
    · exact h1
    · have heq : (σ last).1 = n :=
        le_antisymm (mem_Icc.mp (σ last).2).2
          (Nat.le_of_dvd (by have := (mem_Icc.mp (σ last).2).1; omega) hd)
      exact False.elim (hentry.2 ⟨rfl, heq⟩)
  exact congrArg Subtype.val (σ.injective (Subtype.ext (hi.trans himage.symm)))

private lemma divisor_invariant {n : ℕ} (σ : Equiv.Perm (Index n))
    (hσ : ∀ k, B n k (σ k) = 1) (i : Index n) :
    i.1 ∣ n ↔ (σ i).1 ∣ n := by
  have back : ∀ j : Index n, j.1 ∣ n → (σ.symm j).1 ∣ n := by
    intro j hj
    have h := ((entry_one (σ.symm j) j).mp (by simpa using hσ (σ.symm j))).1
    rcases h with h | h
    · rw [first_column σ hσ (σ.symm j) (by simpa using h)]
    · exact h.trans hj
  exact ⟨Equiv.Perm.perm_symm_on_of_perm_on_finite (f := σ.symm) back,
    fun hi => by simpa using back (σ i) hi⟩

private lemma nondivisor_fixed {n : ℕ} (σ : Equiv.Perm (Index n))
    (hσ : ∀ k, B n k (σ k) = 1) (i : Index n) (hi : ¬ i.1 ∣ n) : σ i = i := by
  classical
  let w : Index n → ℕ := fun j => if j.1 ∣ n then 0 else j.1
  have hle (j : Index n) : w j ≤ w (σ j) := by
    by_cases hj : j.1 ∣ n
    · simp [w, hj]
    · have hout := mt (divisor_invariant σ hσ j).mpr hj
      have he := (entry_one j (σ j)).mp (hσ j)
      rcases he.1 with h1 | hd
      · exact False.elim (hout (by rw [h1]; exact one_dvd n))
      · simpa [w, hj, hout] using
          Nat.le_of_dvd (by have := (mem_Icc.mp (σ j).2).1; omega) hd
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp
    (Equiv.sum_comp σ w).symm i (mem_univ i)
  have hout := mt (divisor_invariant σ hσ i).mpr hi
  apply Subtype.ext
  simpa [w, hi, hout] using heq.symm

private lemma chain_witness {n : ℕ} (hn : 2 ≤ n) (i j : Index n)
    (hij : i.1 < j.1) (hd : i.1 ∣ j.1) (hjn : j.1 ∣ n) :
    ∃ σ : Equiv.Perm (Index n), σ i = j ∧ ∀ k, B n k (σ k) = 1 := by
  classical
  let first : Index n := ⟨1, by simp; omega⟩
  let last : Index n := ⟨n, by simp; omega⟩
  let σ := Equiv.swap first i * Equiv.swap i j * Equiv.swap j last
  have hi := mem_Icc.mp i.2
  have hj := mem_Icc.mp j.2
  have hij' : i ≠ j := fun h => by have := congrArg Subtype.val h; omega
  have hilast : i ≠ last := fun h => by have := congrArg Subtype.val h; dsimp [last] at this; omega
  have hjfirst : j ≠ first := fun h => by have := congrArg Subtype.val h; dsimp [first] at this; omega
  have hfl : first ≠ last := fun h => by
    have := congrArg Subtype.val h; dsimp [first, last] at this; omega
  have hsi : σ i = j := by
    simp [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hij', hilast,
      hjfirst, Ne.symm hij']
  have hsl : σ last = first := by
    by_cases hjl : j = last
    · simp [σ, Equiv.Perm.mul_apply, hjl, Equiv.swap_apply_def, Ne.symm hilast]
    · simp [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Ne.symm hjl, hij',
        Ne.symm hij', hilast]
  refine ⟨σ, hsi, ?_⟩
  intro k
  have hk := mem_Icc.mp k.2
  apply (entry_one k (σ k)).mpr
  by_cases hkl : k = last
  · rw [hkl, hsl]
    exact ⟨Or.inl rfl, by change ¬(n = n ∧ 1 = n); omega⟩
  · have hkn : k.1 ≠ n := fun h => hkl (Subtype.ext h)
    refine ⟨?_, fun h => hkn h.1⟩
    by_cases hki : k = i
    · subst k
      rw [hsi]
      exact Or.inr hd
    by_cases hkf : k = first
    · right
      rw [hkf]
      exact one_dvd _
    by_cases hkj : k = j
    · have hjl : j ≠ last := by simpa [hkj] using hkl
      have hs : σ j = last := by
        rw [show σ j = Equiv.swap first i (Equiv.swap i j last) by
          simp [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hjl]]
        simp [Equiv.swap_apply_def, Ne.symm hilast, Ne.symm hfl, hjl.symm]
      rw [hkj, hs]
      exact Or.inr hjn
    · have hs : σ k = k := by
        simp [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hkf, hki, hkj, hkl]
      rw [hs]
      exact Or.inr (dvd_refl _)

private lemma support_iff {n : ℕ} (hn : 2 ≤ n) (i j : Index n) :
    (i, j) ∈ contributingPositions n ↔
      (i.1 = j.1 ∧ i.1 ≠ 1 ∧ i.1 ≠ n) ∨
      (i.1 = n ∧ j.1 = 1) ∨ (i.1 < j.1 ∧ i.1 ∣ j.1 ∧ j.1 ∣ n) := by
  classical
  simp only [contributingPositions, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨σ, hσij, hσ⟩
    have he := (entry_one i j).mp (hσij ▸ hσ i)
    by_cases hji : i = j
    · left
      refine ⟨congrArg Subtype.val hji, ?_, ?_⟩
      · intro hi
        have hh : (σ i).1 = 1 := by rw [hσij, ← hji]; exact hi
        have := first_column σ hσ i hh
        omega
      · intro hi
        exact he.2 ⟨hi, (congrArg Subtype.val hji).symm.trans hi⟩
    · by_cases hj1 : j.1 = 1
      · exact Or.inr (Or.inl ⟨first_column σ hσ i (by simpa [hσij] using hj1), hj1⟩)
      · have hd : i.1 ∣ j.1 := he.1.resolve_left hj1
        have hjn : j.1 ∣ n := by
          by_contra hjn
          have hin : ¬ i.1 ∣ n := by
            apply mt (divisor_invariant σ hσ i).mp
            rwa [hσij]
          exact hji ((nondivisor_fixed σ hσ i hin).symm.trans hσij)
        exact Or.inr (Or.inr ⟨lt_of_le_of_ne
          (Nat.le_of_dvd (by have := (mem_Icc.mp j.2).1; omega) hd)
          (fun h => hji (Subtype.ext h)), hd, hjn⟩)
  · intro h
    let first : Index n := ⟨1, by simp; omega⟩
    let last : Index n := ⟨n, by simp; omega⟩
    have hswap : ∀ k, B n k (Equiv.swap first last k) = 1 := by
      intro k
      have hk := mem_Icc.mp k.2
      apply (entry_one k _).mpr
      by_cases hkf : k = first
      · rw [hkf, Equiv.swap_apply_left]
        exact ⟨Or.inr (one_dvd n), by change ¬(1 = n ∧ n = n); omega⟩
      by_cases hkl : k = last
      · rw [hkl, Equiv.swap_apply_right]
        exact ⟨Or.inl rfl, by change ¬(n = n ∧ 1 = n); omega⟩
      rw [Equiv.swap_apply_of_ne_of_ne hkf hkl]
      exact ⟨Or.inr (dvd_refl _), fun h => hkl (Subtype.ext h.1)⟩
    rcases h with h | h | h
    · refine ⟨Equiv.swap first last, ?_, hswap⟩
      have hif : i ≠ first := fun e => h.2.1 (congrArg Subtype.val e)
      have hil : i ≠ last := fun e => h.2.2 (congrArg Subtype.val e)
      simpa [Equiv.swap_apply_of_ne_of_ne hif hil] using (Subtype.ext h.1 : i = j)
    · refine ⟨Equiv.swap first last, ?_, hswap⟩
      have hi : i = last := Subtype.ext h.1
      have hj : j = first := Subtype.ext h.2
      simp [hi, hj]
    · exact chain_witness hn i j h.1 h.2.1 h.2.2

private lemma closed_form (n : ℕ) (hn : 2 ≤ n) :
    a n = n - 1 + ∑ d ∈ n.divisors, (d.divisors.card - 1) := by
  classical
  have hn0 : n ≠ 0 := by omega
  let diag : Finset (ℕ × ℕ) := (Ioo 1 n).diag
  let edges : Finset (ℕ × ℕ) := n.divisors.biUnion fun d =>
    d.properDivisors.image fun c => (c, d)
  let S : Finset (ℕ × ℕ) := (diag ∪ {(n, 1)}) ∪ edges
  have mem_diag (x y : ℕ) : (x, y) ∈ diag ↔ x = y ∧ 1 < x ∧ x < n := by
    simp only [diag, Finset.mem_diag, mem_Ioo]
    tauto
  have mem_edges (x y : ℕ) :
      (x, y) ∈ edges ↔ x < y ∧ x ∣ y ∧ y ∣ n := by
    constructor
    · intro h
      obtain ⟨d, hd, h⟩ := mem_biUnion.mp h
      obtain ⟨c, hc, h⟩ := mem_image.mp h
      have hcx : c = x := congrArg Prod.fst h
      have hdy : d = y := congrArg Prod.snd h
      subst x
      subst y
      exact ⟨(Nat.mem_properDivisors.mp hc).2,
        (Nat.mem_properDivisors.mp hc).1, (Nat.mem_divisors.mp hd).1⟩
    · rintro ⟨hxy, hcd, hdn⟩
      exact mem_biUnion.mpr ⟨y, Nat.mem_divisors.mpr ⟨hdn, hn0⟩,
        mem_image.mpr ⟨x, Nat.mem_properDivisors.mpr ⟨hcd, hxy⟩, rfl⟩⟩
  have mem_S (x y : ℕ) : (x, y) ∈ S ↔
      (x = y ∧ 1 < x ∧ x < n) ∨ (x = n ∧ y = 1) ∨
      (x < y ∧ x ∣ y ∧ y ∣ n) := by
    simp only [S, mem_union, mem_diag, mem_edges, mem_singleton, Prod.mk.injEq]
    tauto
  have ha : a n = S.card := by
    unfold a
    apply card_bij (fun p _ => (p.1.1, p.2.1))
    · intro p hp
      apply (mem_S _ _).mpr
      have hi := mem_Icc.mp p.1.2
      have hj := mem_Icc.mp p.2.2
      rcases (support_iff hn p.1 p.2).mp hp with h | h | h
      · exact Or.inl ⟨h.1, by omega, by omega⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro p hp q hq h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    · rintro ⟨x, y⟩ hp
      have hbounds : 1 ≤ x ∧ x ≤ n ∧ 1 ≤ y ∧ y ≤ n := by
        rcases (mem_S x y).mp hp with h | h | h
        · omega
        · omega
        · have hypos : 0 < y := Nat.pos_of_mem_divisors
            (Nat.mem_divisors.mpr ⟨h.2.2, hn0⟩)
          have hyle : y ≤ n := Nat.le_of_dvd (by omega) h.2.2
          have hxpos : 0 < x := Nat.pos_of_dvd_of_pos h.2.1 hypos
          omega
      let i : Index n := ⟨x, mem_Icc.mpr ⟨hbounds.1, hbounds.2.1⟩⟩
      let j : Index n := ⟨y, mem_Icc.mpr ⟨hbounds.2.2.1, hbounds.2.2.2⟩⟩
      refine ⟨(i, j), (support_iff hn i j).mpr ?_, rfl⟩
      change (x = y ∧ x ≠ 1 ∧ x ≠ n) ∨
        (x = n ∧ y = 1) ∨ (x < y ∧ x ∣ y ∧ y ∣ n)
      rcases (mem_S x y).mp hp with h | h | h
      · exact Or.inl ⟨h.1, by omega, by omega⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hdiagcard : diag.card = n - 2 := by
    dsimp only [diag]
    rw [Finset.diag_card, Nat.card_Ioo]
    omega
  have hedgecard : edges.card = ∑ d ∈ n.divisors, (d.divisors.card - 1) := by
    dsimp only [edges]
    rw [card_biUnion]
    · apply sum_congr rfl
      intro d hd
      rw [card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      rw [← Nat.insert_self_properDivisors hd0,
        card_insert_of_notMem Nat.self_notMem_properDivisors]
      simp
    · intro d hd e he hde
      apply disjoint_left.mpr
      intro p hp hq
      obtain ⟨c, hc, hcp⟩ := mem_image.mp hp
      obtain ⟨c', hc', hc'p⟩ := mem_image.mp hq
      exact hde (congrArg Prod.snd (hcp.trans hc'p.symm))
  have hdisdiag : Disjoint diag {(n, 1)} := by
    apply disjoint_left.mpr
    rintro ⟨x, y⟩ hp hq
    have h := (mem_diag x y).mp hp
    have h' := Prod.mk.inj (mem_singleton.mp hq)
    omega
  have hdisedges : Disjoint (diag ∪ {(n, 1)}) edges := by
    apply disjoint_left.mpr
    rintro ⟨x, y⟩ hp hq
    have h := (mem_edges x y).mp hq
    rcases mem_union.mp hp with hp | hp
    · have h' := (mem_diag x y).mp hp
      omega
    · have h' := Prod.mk.inj (mem_singleton.mp hp)
      omega
  rw [ha]
  change ((diag ∪ {(n, 1)}) ∪ edges).card = _
  rw [card_union_of_disjoint hdisedges, card_union_of_disjoint hdisdiag,
    hdiagcard, card_singleton, hedgecard]
  omega

/-- The published twenty-value list is false: the value at index twenty is 31, not 30. -/
theorem result : ¬ claim := by
  intro h
  have h20 : a 20 = 30 := h.2.2.2.2.2.2.2.2.2.1
  have hc := closed_form 20 (by norm_num)
  have hcalc : 20 - 1 + ∑ d ∈ (20 : ℕ).divisors, (d.divisors.card - 1) = 31 := by
    decide
  rw [hcalc] at hc
  omega

end D5.S3.Arith.GranvikRedhefferSupport
