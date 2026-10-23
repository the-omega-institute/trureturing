/- GID: D5/S3/Combinatorics/Permutation/PackingMaximumRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/PackingMaximumRefutation
   mirror-E: none(waiver:kernel-checked-finite-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.claim; result=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result; claim=D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.claim
   digest: The prescribed interleaved pattern need not maximize the packing count. -/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # A finite refutation of the whole packing-maximum assertion

Permutations use zero-based ranks and positions. The source labels are obtained by
adding one; every strict comparison and every prescribed window is unchanged.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.PackingMaximumRefutation

/-- Zero-based one-line entries, with an irrelevant default outside the word. -/
def entry {n : ℕ} (w : Fin n → Fin n) (i : ℕ) : ℕ :=
  (List.ofFn fun k => (w k).val).getD i 0

/-- Each prescribed window position lies in the exact source permutation length. -/
def windowIndex (K m j : ℕ) (t : Fin j) (a : Fin K) :
    Fin (K + (j - 1) * (K - m)) :=
  ⟨t.val * (K - m) + a.val, by
    have ht : t.val ≤ j - 1 := by omega
    have hm := Nat.mul_le_mul_right (K - m) ht
    omega⟩

/-- All strict comparisons in all regularly prescribed windows; extras are allowed. -/
def Packs {K : ℕ} (p : Fin K → Fin K) (m j : ℕ)
    (w : Fin (K + (j - 1) * (K - m)) → Fin (K + (j - 1) * (K - m))) : Prop :=
  ∀ t : Fin j, ∀ a b : Fin K,
    (w (windowIndex K m j t a) < w (windowIndex K m j t b) ↔ p a < p b)

/-- Actual permutations, without a quotient or an occurrence-avoidance condition. -/
def SourcePacking {K : ℕ} (p : Fin K → Fin K) (m j : ℕ) :=
  {w : Equiv.Perm (Fin (K + (j - 1) * (K - m))) // Packs p m j w}

/-- The original packing cardinality. -/
noncomputable def count {K : ℕ} (p : Fin K → Fin K) (m j : ℕ) : ℕ :=
  Nat.card (SourcePacking p m j)

/-- Prefix and suffix have exactly the same relative order, as the source assumes. -/
def Admissible {K : ℕ} (p : Fin K → Fin K) (m : ℕ) : Prop :=
  Function.Injective p ∧
    ∀ a b : Fin m,
      (entry p a.val < entry p b.val ↔
        entry p (K - m + a.val) < entry p (K - m + b.val))

/-- The prescribed odd prefix and even suffix; the middle is unrestricted. -/
def Prescribed {K : ℕ} (p : Fin K → Fin K) (m : ℕ) : Prop :=
  (∀ a : Fin m, entry p a.val = 2 * a.val) ∧
  (∀ a : Fin m, entry p (K - m + a.val) = 2 * a.val + 1)

/-- Literal maximum attainment in the entire source parameter domain. -/
noncomputable def claim : Prop :=
  ∀ K m j : ℕ, 2 ≤ K → 1 ≤ m → m < K → 2 * m ≤ K → 1 ≤ j →
    ∃ rho : Fin K → Fin K, Admissible rho m ∧ Prescribed rho m ∧
      ∀ pi : Fin K → Fin K, Admissible pi m → count pi m j ≤ count rho m j

/-- The competitor 13472568, with values shifted down by one. -/
def competitor : Fin 8 → Fin 8 := ![0, 2, 3, 6, 1, 4, 5, 7]

/-- The prescribed pattern 13572468, with values shifted down by one. -/
def prescribed : Fin 8 → Fin 8 := ![0, 2, 4, 6, 1, 3, 5, 7]

private def piCertificate : Finset (Fin 12 → Fin 12) :=
  {![0, 2, 3, 7, 1, 5, 6, 10, 4, 8, 9, 11],
   ![0, 2, 3, 8, 1, 5, 6, 10, 4, 7, 9, 11],
   ![0, 2, 3, 9, 1, 5, 6, 10, 4, 7, 8, 11],
   ![0, 2, 4, 7, 1, 5, 6, 10, 3, 8, 9, 11],
   ![0, 2, 4, 8, 1, 5, 6, 10, 3, 7, 9, 11],
   ![0, 2, 4, 9, 1, 5, 6, 10, 3, 7, 8, 11],
   ![0, 3, 4, 7, 1, 5, 6, 10, 2, 8, 9, 11],
   ![0, 3, 4, 8, 1, 5, 6, 10, 2, 7, 9, 11],
   ![0, 3, 4, 9, 1, 5, 6, 10, 2, 7, 8, 11]}

private lemma pi_complete (w : Fin 12 → Fin 12)
    (hi : Function.Injective w)
    (h0 : w 0 < w 4)
    (h1 : w 4 < w 1)
    (h2 : w 1 < w 2)
    (h3 : w 2 < w 5)
    (h4 : w 5 < w 6)
    (h5 : w 6 < w 3)
    (h6 : w 3 < w 7)
    (h7 : w 4 < w 8)
    (h8 : w 8 < w 5)
    (h9 : w 5 < w 6)
    (h10 : w 6 < w 9)
    (h11 : w 9 < w 10)
    (h12 : w 10 < w 7)
    (h13 : w 7 < w 11)
    : w ∈ piCertificate := by
  have ne1_8 : (w 1).val ≠ (w 8).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have ne2_8 : (w 2).val ≠ (w 8).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have ne3_9 : (w 3).val ≠ (w 9).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have ne3_10 : (w 3).val ≠ (w 10).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have fixed : (w 0).val = 0 ∧ (w 4).val = 1 ∧ (w 5).val = 5 ∧ (w 6).val = 6 ∧ (w 7).val = 10 ∧ (w 11).val = 11 := by omega
  have a : ((w 1).val = 2 ∧ (w 2).val = 3 ∧ (w 8).val = 4) ∨ ((w 1).val = 2 ∧ (w 2).val = 4 ∧ (w 8).val = 3) ∨ ((w 1).val = 3 ∧ (w 2).val = 4 ∧ (w 8).val = 2) := by omega
  have b : ((w 3).val = 7 ∧ (w 9).val = 8 ∧ (w 10).val = 9) ∨ ((w 3).val = 8 ∧ (w 9).val = 7 ∧ (w 10).val = 9) ∨ ((w 3).val = 9 ∧ (w 9).val = 7 ∧ (w 10).val = 8) := by omega
  rcases a with a | a | a <;> rcases b with b | b | b
  · have hw : w = ![0, 2, 3, 7, 1, 5, 6, 10, 4, 8, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 3, 8, 1, 5, 6, 10, 4, 7, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 3, 9, 1, 5, 6, 10, 4, 7, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 4, 7, 1, 5, 6, 10, 3, 8, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 4, 8, 1, 5, 6, 10, 3, 7, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 4, 9, 1, 5, 6, 10, 3, 7, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 4, 7, 1, 5, 6, 10, 2, 8, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 4, 8, 1, 5, 6, 10, 2, 7, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 4, 9, 1, 5, 6, 10, 2, 7, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel


private def rhoCertificate : Finset (Fin 12 → Fin 12) :=
  {![0, 2, 5, 8, 1, 4, 7, 10, 3, 6, 9, 11],
   ![0, 2, 5, 9, 1, 4, 7, 10, 3, 6, 8, 11],
   ![0, 2, 6, 8, 1, 4, 7, 10, 3, 5, 9, 11],
   ![0, 2, 6, 9, 1, 4, 7, 10, 3, 5, 8, 11],
   ![0, 3, 5, 8, 1, 4, 7, 10, 2, 6, 9, 11],
   ![0, 3, 5, 9, 1, 4, 7, 10, 2, 6, 8, 11],
   ![0, 3, 6, 8, 1, 4, 7, 10, 2, 5, 9, 11],
   ![0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11]}

private lemma rho_complete (w : Fin 12 → Fin 12)
    (hi : Function.Injective w)
    (h0 : w 0 < w 4)
    (h1 : w 4 < w 1)
    (h2 : w 1 < w 5)
    (h3 : w 5 < w 2)
    (h4 : w 2 < w 6)
    (h5 : w 6 < w 3)
    (h6 : w 3 < w 7)
    (h7 : w 4 < w 8)
    (h8 : w 8 < w 5)
    (h9 : w 5 < w 9)
    (h10 : w 9 < w 6)
    (h11 : w 6 < w 10)
    (h12 : w 10 < w 7)
    (h13 : w 7 < w 11)
    : w ∈ rhoCertificate := by
  have ne1_8 : (w 1).val ≠ (w 8).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have ne2_9 : (w 2).val ≠ (w 9).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have ne3_10 : (w 3).val ≠ (w 10).val := by
    intro he; have := hi (Fin.ext he); norm_num at this
  have fixed : (w 0).val = 0 ∧ (w 4).val = 1 ∧ (w 5).val = 4 ∧ (w 6).val = 7 ∧ (w 7).val = 10 ∧ (w 11).val = 11 := by omega
  have a : ((w 1).val = 2 ∧ (w 8).val = 3) ∨ ((w 1).val = 3 ∧ (w 8).val = 2) := by omega
  have b : ((w 2).val = 5 ∧ (w 9).val = 6) ∨ ((w 2).val = 6 ∧ (w 9).val = 5) := by omega
  have c : ((w 3).val = 8 ∧ (w 10).val = 9) ∨ ((w 3).val = 9 ∧ (w 10).val = 8) := by omega
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
  · have hw : w = ![0, 2, 5, 8, 1, 4, 7, 10, 3, 6, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 5, 9, 1, 4, 7, 10, 3, 6, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 6, 8, 1, 4, 7, 10, 3, 5, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 2, 6, 9, 1, 4, 7, 10, 3, 5, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 5, 8, 1, 4, 7, 10, 2, 6, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 5, 9, 1, 4, 7, 10, 2, 6, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 6, 8, 1, 4, 7, 10, 2, 5, 9, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel
  · have hw : w = ![0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11] := by
      funext i
      apply Fin.ext
      fin_cases i <;> dsimp <;> omega
    rw [hw]
    decide +kernel



/-- Rank assignments and actual source permutations correspond in both directions. -/
noncomputable def encodingEquiv {K : ℕ} (p : Fin K → Fin K) (m j : ℕ) :
    SourcePacking p m j ≃
      {w : Fin (K + (j - 1) * (K - m)) → Fin (K + (j - 1) * (K - m)) //
        Function.Injective w ∧ Packs p m j w} where
  toFun w := ⟨w.val, w.val.injective, w.property⟩
  invFun w := ⟨Equiv.ofBijective w.val (Finite.injective_iff_bijective.mp w.property.1),
    w.property.2⟩
  left_inv w := by apply Subtype.ext; apply Equiv.ext; intro i; rfl
  right_inv w := by apply Subtype.ext; rfl

/-- No labeling factor is introduced by the rank-assignment representation. -/
theorem source_cardinality {K : ℕ} (m j : ℕ) (p : Fin K → Fin K) :
    count p m j = Nat.card
      {w : Fin (K + (j - 1) * (K - m)) → Fin (K + (j - 1) * (K - m)) //
        Function.Injective w ∧ Packs p m j w} :=
  Nat.card_congr (encodingEquiv p m j)

private lemma pi_membership (w : Fin 12 → Fin 12) :
    w ∈ piCertificate ↔ Function.Injective w ∧ Packs competitor 4 2 w := by
  constructor
  · intro hw
    simp only [piCertificate, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Packs Function.Injective <;> decide +kernel
  · rintro ⟨hi, h⟩
    have h0 := (h 0 0 4).2 (by decide)
    change w 0 < w 4 at h0
    have h1 := (h 0 4 1).2 (by decide)
    change w 4 < w 1 at h1
    have h2 := (h 0 1 2).2 (by decide)
    change w 1 < w 2 at h2
    have h3 := (h 0 2 5).2 (by decide)
    change w 2 < w 5 at h3
    have h4 := (h 0 5 6).2 (by decide)
    change w 5 < w 6 at h4
    have h5 := (h 0 6 3).2 (by decide)
    change w 6 < w 3 at h5
    have h6 := (h 0 3 7).2 (by decide)
    change w 3 < w 7 at h6
    have h7 := (h 1 0 4).2 (by decide)
    change w 4 < w 8 at h7
    have h8 := (h 1 4 1).2 (by decide)
    change w 8 < w 5 at h8
    have h9 := (h 1 1 2).2 (by decide)
    change w 5 < w 6 at h9
    have h10 := (h 1 2 5).2 (by decide)
    change w 6 < w 9 at h10
    have h11 := (h 1 5 6).2 (by decide)
    change w 9 < w 10 at h11
    have h12 := (h 1 6 3).2 (by decide)
    change w 10 < w 7 at h12
    have h13 := (h 1 3 7).2 (by decide)
    change w 7 < w 11 at h13
    exact pi_complete w hi h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

/-- The exact original packing count for 13472568. -/
theorem count_competitor : count competitor 4 2 = 9 := by
  classical
  rw [source_cardinality, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype piCertificate pi_membership]
  decide +kernel

private lemma rho_membership (w : Fin 12 → Fin 12) :
    w ∈ rhoCertificate ↔ Function.Injective w ∧ Packs prescribed 4 2 w := by
  constructor
  · intro hw
    simp only [rhoCertificate, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Packs Function.Injective <;> decide +kernel
  · rintro ⟨hi, h⟩
    have h0 := (h 0 0 4).2 (by decide)
    change w 0 < w 4 at h0
    have h1 := (h 0 4 1).2 (by decide)
    change w 4 < w 1 at h1
    have h2 := (h 0 1 5).2 (by decide)
    change w 1 < w 5 at h2
    have h3 := (h 0 5 2).2 (by decide)
    change w 5 < w 2 at h3
    have h4 := (h 0 2 6).2 (by decide)
    change w 2 < w 6 at h4
    have h5 := (h 0 6 3).2 (by decide)
    change w 6 < w 3 at h5
    have h6 := (h 0 3 7).2 (by decide)
    change w 3 < w 7 at h6
    have h7 := (h 1 0 4).2 (by decide)
    change w 4 < w 8 at h7
    have h8 := (h 1 4 1).2 (by decide)
    change w 8 < w 5 at h8
    have h9 := (h 1 1 5).2 (by decide)
    change w 5 < w 9 at h9
    have h10 := (h 1 5 2).2 (by decide)
    change w 9 < w 6 at h10
    have h11 := (h 1 2 6).2 (by decide)
    change w 6 < w 10 at h11
    have h12 := (h 1 6 3).2 (by decide)
    change w 10 < w 7 at h12
    have h13 := (h 1 3 7).2 (by decide)
    change w 7 < w 11 at h13
    exact rho_complete w hi h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

/-- The exact original packing count for 13572468. -/
theorem count_prescribed : count prescribed 4 2 = 8 := by
  classical
  rw [source_cardinality, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype rhoCertificate rho_membership]
  decide +kernel

/-- The entire prescribed family at K=2m=8 consists of this one pattern. -/
theorem prescribed_boundary (p : Fin 8 → Fin 8) (h : Prescribed p 4) :
    p = prescribed := by
  have h0 := h.1 0
  have h1 := h.1 1
  have h2 := h.1 2
  have h3 := h.1 3
  have h4 := h.2 0
  have h5 := h.2 1
  have h6 := h.2 2
  have h7 := h.2 3
  change (p 0).val = 0 at h0
  change (p 1).val = 2 at h1
  change (p 2).val = 4 at h2
  change (p 3).val = 6 at h3
  change (p 4).val = 1 at h4
  change (p 5).val = 3 at h5
  change (p 6).val = 5 at h6
  change (p 7).val = 7 at h7
  funext i
  apply Fin.ext
  fin_cases i <;> first
    | exact h0
    | exact h1
    | exact h2
    | exact h3
    | exact h4
    | exact h5
    | exact h6
    | exact h7

/-- Whole-Conjecture 7.1 refutation, with the source's existential maximum reading. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨rho, _, hp, hmax⟩ := h 8 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hr := prescribed_boundary rho hp
  have hi : Admissible competitor 4 := by
    unfold Admissible Function.Injective
    decide +kernel
  have hh := hmax competitor hi
  rw [hr, count_competitor, count_prescribed] at hh
  omega

end D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
