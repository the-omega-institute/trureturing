/- GID: D5/S3/Arith/Additive/MaximalSidon
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/MaximalSidon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Prod, mathlib/module/Mathlib.Data.Fintype.Basic, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Insertion obstructions for maximal Sidon subsets are counted by an explicit cubic polynomial -/

import D5.S3.Arith.Additive.SidonSet

set_option autoImplicit false

namespace D5.S3.Arith.Additive.MaximalSidon

open D5.S3.Arith.Additive.SidonSet

/-- A Sidon set maximal in `[1,N]` has size bounded by the insertion-obstruction
polynomial `A.card ^ 3 + A.card ^ 2 + A.card`. -/
theorem card_le_of_maximal (A : Finset ℕ) (N : ℕ)
    (_hA : A ⊆ Finset.Icc 1 N)
    (hSidon : IsSidon (A : Set ℕ))
    (hmax : ∀ x ∈ Finset.Icc 1 N, x ∉ A →
      ¬ IsSidon (insert x A : Set ℕ)) :
    N ≤ A.card ^ 3 + A.card ^ 2 + A.card := by
  have hcollision (x : ℕ) (hbad : ¬ IsSidon (insert x A : Set ℕ)) :
      (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x + a = b + c) ∨
        (∃ b ∈ A, ∃ c ∈ A, 2 * x = b + c) := by
    have hxA : x ∉ A := by
      intro hx
      have heq : (insert x A : Set ℕ) = (A : Set ℕ) := by
        ext y
        simp [hx]
      apply hbad
      rw [heq]
      exact hSidon
    rw [IsSidon] at hbad
    push Not at hbad
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, hbd⟩ := hbad
    have ha' : a = x ∨ a ∈ A := by simpa using ha
    have hb' : b = x ∨ b ∈ A := by simpa using hb
    have hc' : c = x ∨ c ∈ A := by simpa using hc
    have hd' : d = x ∨ d ∈ A := by simpa using hd
    rcases ha' with hax | ha
    · subst a
      rcases hb' with hbx | hb
      · subst b
        rcases hc' with hcx | hc
        · subst c
          rcases hd' with hdx | hd
          · subst d
            exact (hbd rfl rfl).elim
          · exact (hxA (by omega)).elim
        · rcases hd' with hdx | hd
          · subst d
            exact (hxA (by omega)).elim
          · exact Or.inr ⟨c, hc, d, hd, by omega⟩
      · rcases hc' with hcx | hc
        · subst c
          rcases hd' with hdx | hd
          · subst d
            exact (hac rfl (by omega)).elim
          · exact (hac rfl (by omega)).elim
        · rcases hd' with hdx | hd
          · subst d
            exact (hbd rfl (by omega)).elim
          · exact Or.inl ⟨b, hb, c, hc, d, hd, by omega⟩
    · rcases hb' with hbx | hb
      · subst b
        rcases hc' with hcx | hc
        · subst c
          rcases hd' with hdx | hd
          · subst d
            exact (hbd (by omega) rfl).elim
          · exact (hbd (by omega) (by omega)).elim
        · rcases hd' with hdx | hd
          · subst d
            exact (hac (by omega) rfl).elim
          · exact Or.inl ⟨a, ha, c, hc, d, hd, by omega⟩
      · rcases hc' with hcx | hc
        · subst c
          rcases hd' with hdx | hd
          · subst d
            exact Or.inr ⟨a, ha, b, hb, by omega⟩
          · exact Or.inl ⟨d, hd, a, ha, b, hb, by omega⟩
        · rcases hd' with hdx | hd
          · subst d
            exact Or.inl ⟨c, hc, a, ha, b, hb, by omega⟩
          · rcases hSidon ha hb hc hd hab with h | h
            · exact (hac h.1 h.2).elim
            · exact (hbd h.1 h.2).elim
  let T : Finset ℕ :=
    (A ×ˢ (A ×ˢ A)).image (fun p => p.2.1 + p.2.2 - p.1)
  let P : Finset ℕ :=
    (A ×ˢ A).image (fun p => (p.1 + p.2) / 2)
  have hsub : Finset.Icc 1 N ⊆ A ∪ T ∪ P := by
    intro x hx
    by_cases hxa : x ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxa)
    · rcases hcollision x (hmax x hx hxa) with h | h
      · rcases h with ⟨a, ha, b, hb, c, hc, heq⟩
        apply Finset.mem_union_left _
        apply Finset.mem_union_right A
        apply Finset.mem_image.mpr
        refine ⟨(a, (b, c)), ?_, ?_⟩
        · simp only [Finset.mem_product]
          exact ⟨ha, hb, hc⟩
        · dsimp [T]
          omega
      · rcases h with ⟨b, hb, c, hc, heq⟩
        apply Finset.mem_union_right (A ∪ T)
        apply Finset.mem_image.mpr
        refine ⟨(b, c), ?_, ?_⟩
        · exact Finset.mem_product.mpr ⟨hb, hc⟩
        · dsimp [P]
          omega
  have hcard := Finset.card_le_card hsub
  have hunion : (A ∪ T ∪ P).card ≤ A.card + T.card + P.card := by
    calc
      (A ∪ T ∪ P).card ≤ (A ∪ T).card + P.card := Finset.card_union_le _ _
      _ ≤ (A.card + T.card) + P.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = A.card + T.card + P.card := by omega
  have hT : T.card ≤ A.card ^ 3 := by
    dsimp [T]
    calc
      ((A ×ˢ (A ×ˢ A)).image (fun p => p.2.1 + p.2.2 - p.1)).card ≤
          (A ×ˢ (A ×ˢ A)).card := Finset.card_image_le
      _ = A.card ^ 3 := by
        simp [Finset.card_product, pow_succ, Nat.mul_comm]
  have hP : P.card ≤ A.card ^ 2 := by
    dsimp [P]
    calc
      ((A ×ˢ A).image (fun p => (p.1 + p.2) / 2)).card ≤ (A ×ˢ A).card :=
        Finset.card_image_le
      _ = A.card ^ 2 := by simp [Finset.card_product, pow_two]
  have hN : N ≤ A.card + T.card + P.card := by
    calc
      N = (Finset.Icc 1 N).card := by simp [Nat.card_Icc]
      _ ≤ (A ∪ T ∪ P).card := hcard
      _ ≤ A.card + T.card + P.card := hunion
  omega

end D5.S3.Arith.Additive.MaximalSidon
