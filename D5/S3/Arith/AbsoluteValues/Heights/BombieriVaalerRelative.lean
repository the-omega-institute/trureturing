/- GID: D5/S3/Arith/AbsoluteValues/Heights/BombieriVaalerRelative
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/BombieriVaalerRelative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: From numbers at least one, select a smaller subfamily with bounded geometric mean. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.BombieriVaalerMaxNorm
public import D5.S3.Arith.AbsoluteValues.Heights.RowEntryHeight
public import D5.S3.Arith.AbsoluteValues.Heights.RestrictScalars

public section

open Finset Matrix Module NumberField Real

namespace Real

private lemma prod_range_pow_le {k : ℕ} (G : ℕ → ℝ) (h1 : ∀ i, 1 ≤ G i)
    (hm : ∀ a b, a ≤ b → b < k → G a ≤ G b) {k' : ℕ} (hk' : k' ≤ k) :
    (∏ i ∈ Finset.range k', G i) ^ k ≤ (∏ i ∈ Finset.range k, G i) ^ k' := by
  rcases eq_or_lt_of_le hk' with rfl | hlt
  · exact le_rfl
  set P₁ := ∏ i ∈ Finset.range k', G i with hP1def
  set P₂ := ∏ i ∈ Finset.Ico k' k, G i with hP2def
  have hP : P₁ * P₂ = ∏ i ∈ Finset.range k, G i := Finset.prod_range_mul_prod_Ico G hk'
  have hP1 : 1 ≤ P₁ := Finset.one_le_prod₀ fun i _ ↦ h1 i
  have hP2 : 1 ≤ P₂ := Finset.one_le_prod₀ fun i _ ↦ h1 i
  set c := G k' with hcdef
  have hc1 : 1 ≤ c := h1 k'
  have hub : P₁ ≤ c ^ k' := by
    calc P₁ ≤ ∏ _i ∈ Finset.range k', c :=
          Finset.prod_le_prod₀ (fun i _ ↦ by linarith [h1 i])
            (fun i hi ↦ hm i k' (le_of_lt (Finset.mem_range.1 hi)) hlt)
      _ = c ^ k' := by rw [Finset.prod_const, Finset.card_range]
  have hlb : c ^ (k - k') ≤ P₂ := by
    calc c ^ (k - k') = ∏ _i ∈ Finset.Ico k' k, c := by
          rw [Finset.prod_const, Nat.card_Ico]
      _ ≤ P₂ := Finset.prod_le_prod₀ (fun i _ ↦ by linarith)
            (fun i hi ↦ hm k' i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2)
  have key : P₁ ^ (k - k') ≤ P₂ ^ k' := by
    calc P₁ ^ (k - k') ≤ (c ^ k') ^ (k - k') := pow_le_pow_left₀ (by linarith) hub _
      _ = (c ^ (k - k')) ^ k' := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ P₂ ^ k' := pow_le_pow_left₀ (by positivity) hlb _
  calc P₁ ^ k = P₁ ^ k' * P₁ ^ (k - k') := by rw [← pow_add]; congr 1; omega
    _ ≤ P₁ ^ k' * P₂ ^ k' := by
        have hnn : (0 : ℝ) ≤ P₁ ^ k' := by positivity
        nlinarith
    _ = (P₁ * P₂) ^ k' := (mul_pow _ _ _).symm
    _ = _ := by rw [hP]

/-- **Rearranging by increasing size** (Bombieri–Gubler, in the proof of Theorem 2.9.19). From `k`
numbers, all at least `1`, one can select `k'` of them whose product `T` satisfies
`T ^ k ≤ (∏ all) ^ k'` — the geometric mean of the `k'` smallest is at most the geometric mean of
all `k`. Selecting is an injection `Fin k' → Fin k`, and the proof is the sorting permutation
`Tuple.sort`. -/
theorem exists_injective_prod_pow_le {k : ℕ} (g : Fin k → ℝ) (hg : ∀ l, 1 ≤ g l) {k' : ℕ}
    (hk' : k' ≤ k) :
    ∃ f : Fin k' → Fin k, Function.Injective f ∧
      (∏ l, g (f l)) ^ k ≤ (∏ l, g l) ^ k' := by
  classical
  set s := Tuple.sort g with hsdef
  set G : ℕ → ℝ := fun n ↦ if h : n < k then g (s ⟨n, h⟩) else 1 with hGdef
  have hG1 : ∀ i, 1 ≤ G i := by
    intro i
    rw [hGdef]
    dsimp only
    split
    · exact hg _
    · exact le_rfl
  have hGm : ∀ a b, a ≤ b → b < k → G a ≤ G b := by
    intro a b hab hb
    have ha : a < k := lt_of_le_of_lt hab hb
    simp only [hGdef, ha, hb, ↓reduceDIte]
    exact Tuple.monotone_sort g (show (⟨a, ha⟩ : Fin k) ≤ ⟨b, hb⟩ from hab)
  have e1 : ∏ l : Fin k', g (s (Fin.castLE hk' l)) = ∏ i ∈ Finset.range k', G i := by
    rw [← Fin.prod_univ_eq_prod_range G k']
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    have hl : (l : ℕ) < k := lt_of_lt_of_le l.2 hk'
    simp only [hGdef, hl, ↓reduceDIte]
    rfl
  have e2 : ∏ l : Fin k, g l = ∏ i ∈ Finset.range k, G i := by
    rw [← Fin.prod_univ_eq_prod_range G k, ← Equiv.prod_comp s g]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    simp only [hGdef, l.2, ↓reduceDIte]
  refine ⟨fun l ↦ s (Fin.castLE hk' l), fun a b hab ↦ ?_, ?_⟩
  · exact Fin.castLE_injective hk' (s.injective hab)
  · rw [e1, e2]
    exact prod_range_pow_le G hG1 hGm hk'

end Real

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

end NumberField

section Examples

open Matrix Module NumberField

end Examples

end
