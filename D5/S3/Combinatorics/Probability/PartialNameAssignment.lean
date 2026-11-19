/- GID: D5/S3/Combinatorics/Probability/PartialNameAssignment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/PartialNameAssignment
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Uniform injective namings retain the exact unused-name hit probability after partial observation. -/

import D5.S0.Diagonal.Probability.EquivariantEscape
import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
import Mathlib.Data.Fintype.CardEmbedding

open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Probability.PartialNameAssignment

variable {V N : Type*} [DecidableEq V]

/-- Injections consistent with the fixed names on `K` and the remaining names in `A`. -/
abbrev Candidates (K : Finset V) (A : Finset N) (knownNames : K ↪ N) :=
  {f : V ↪ N // (∀ x : K, f x = knownNames x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A}

/-- Restrict a consistent naming to the remaining vertices. The inverse fills in the fixed names. -/
def residualEmbedding (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (hsep : ∀ x, knownNames x ∉ A) :
    Candidates K A knownNames ≃ ({v // v ∉ K} ↪ A) where
  toFun f := {
    toFun := fun x => ⟨f.1 x, f.2.2 x⟩
    inj' := fun _ _ e => Subtype.ext (f.1.injective (congrArg Subtype.val e)) }
  invFun g := by
    let f (x : V) := if hx : x ∈ K then knownNames ⟨x, hx⟩ else (g ⟨x, hx⟩).1
    refine ⟨⟨f, ?_⟩, ?_, ?_⟩
    · intro x y hxy
      by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
      · simp only [f, dite_eq_left hx, dite_eq_left hy] at hxy
        exact congrArg Subtype.val (knownNames.injective hxy)
      · simp only [f, dite_eq_left hx, dite_eq_right hy] at hxy
        exact (hsep ⟨x, hx⟩ (hxy ▸ (g ⟨y, hy⟩).2)).elim
      · simp only [f, dite_eq_right hx, dite_eq_left hy] at hxy
        exact (hsep ⟨y, hy⟩ (hxy ▸ (g ⟨x, hx⟩).2)).elim
      · simp only [f, dite_eq_right hx, dite_eq_right hy] at hxy
        exact congrArg Subtype.val (g.injective (Subtype.ext hxy))
    · intro x
      change f x = knownNames x
      simp [f, x.2]
    · intro x
      change f x ∈ A
      simpa only [f, dite_eq_right x.2] using (g x).2
  left_inv f := by
    apply Subtype.ext
    ext x
    change (if hx : x ∈ K then knownNames ⟨x, hx⟩ else f.1 x) = f.1 x
    by_cases hx : x ∈ K
    · simpa only [dite_eq_left hx] using (f.2.1 ⟨x, hx⟩).symm
    · simp [hx]
  right_inv g := by
    ext x
    change (if hx : x.1 ∈ K then knownNames ⟨x, hx⟩ else (g ⟨x, hx⟩).1) = (g x).1
    simp [x.2]

open Function

private def embeddingEvalFiberSwap {X Y : Type*} [DecidableEq Y]
    (x : X) (a b : Y) : {f : X ↪ Y // f x = a} ≃ {f : X ↪ Y // f x = b} := by
  let e := Equiv.swap a b
  refine {
    toFun := fun f => ⟨f.1.trans e.toEmbedding, by
      change e (f.1 x) = b
      rw [f.2, Equiv.swap_apply_left]⟩
    invFun := fun f => ⟨f.1.trans e.symm.toEmbedding, by
      change e.symm (f.1 x) = a
      rw [f.2, Equiv.symm_swap, Equiv.swap_apply_right]⟩
    left_inv := fun f => Subtype.ext (Embedding.ext fun y => e.symm_apply_apply (f.1 y))
    right_inv := fun f => Subtype.ext (Embedding.ext fun y => e.apply_symm_apply (f.1 y)) }

private theorem card_embedding_eval_mul {X Y : Type*} [Fintype X] [Fintype Y]
    (x : X) (a : Y) :
    Nat.card {f : X ↪ Y // f x = a} * Fintype.card Y = Fintype.card (X ↪ Y) := by
  classical
  let S (b : Y) := {f : X ↪ Y // f x = b}
  let (b : Y) : Fintype (S b) := Fintype.ofFinite _
  let e : (X ↪ Y) ≃ (Σ b : Y, S b) :=
    { toFun := fun f => ⟨f x, f, rfl⟩
      invFun := fun p => p.2.1
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, f, hf⟩ => by subst_vars; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hcard (b : Y) : Fintype.card (S b) = Nat.card (S a) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (embeddingEvalFiberSwap x b a)
  rw [mul_comm]
  simp only [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

private theorem card_embedding_hit_mul {X Y : Type*} [Fintype X] [Fintype Y] (a : Y) :
    Nat.card {f : X ↪ Y // a ∈ Set.range f} * Fintype.card Y =
      Fintype.card X * Fintype.card (X ↪ Y) := by
  classical
  let S (x : X) := {f : X ↪ Y // f x = a}
  let (x : X) : Fintype (S x) := Fintype.ofFinite _
  let e : (Σ x : X, S x) ≃ {f : X ↪ Y // a ∈ Set.range f} :=
    { toFun := fun ⟨x, f, hf⟩ => ⟨f, x, hf⟩
      invFun := fun f => ⟨f.2.choose, f.1, f.2.choose_spec⟩
      left_inv := fun ⟨x, f, hf⟩ => by
        have hx := f.injective ((show ∃ y, f y = a from ⟨x, hf⟩).choose_spec.trans hf.symm)
        exact Sigma.subtype_ext hx rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma, Finset.sum_mul]
  have hcard (x : X) : Fintype.card (S x) * Fintype.card Y = Fintype.card (X ↪ Y) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_embedding_eval_mul x a
  simp [hcard]

open D5.S0.Diagonal.Probability.EquivariantEscape
    (uniformPmf uniformPmf_toOuterMeasure_apply)
open D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion (uniform_filter)

private def hitEquiv (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (hsep : ∀ x, knownNames x ∉ A) (a : A) :
    {f : Candidates K A knownNames // ∃ x : {v // v ∉ K}, f.1 x = a.1} ≃
      {g : {v // v ∉ K} ↪ A // a ∈ Set.range g} :=
  (residualEmbedding K A knownNames hsep).subtypeEquiv fun f => by
    change (∃ x : {v // v ∉ K}, f.1 x = a.1) ↔
      (∃ x : {v // v ∉ K}, (residualEmbedding K A knownNames hsep) f x = a)
    refine exists_congr fun x => ?_
    change f.1 x = a.1 ↔ (⟨f.1 x, f.2.2 x⟩ : A) = a
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩

/-- Conditioning a uniform injection on the partial naming and available names gives
the uniform law on consistent namings, with hit probability equal to the remaining
vertex count divided by the available name count for each available name. -/
theorem uniform_remaining_name_hit [Fintype V] [Fintype N]
    (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (hsep : ∀ x, knownNames x ∉ A) (h : Nonempty (Candidates K A knownNames)) :
    let availableCount := A.card
    let : Nonempty (V ↪ N) := h.map Subtype.val
    ∃ ν : PMF (Candidates K A knownNames),
      (∀ f, ν f = (Nat.card (Candidates K A knownNames) : ℝ≥0∞)⁻¹) ∧
      (∀ hs, (uniformPmf (V ↪ N)).filter
        {f | (∀ x : K, f x = knownNames x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A} hs =
          ν.map Subtype.val) ∧
      (∀ a : A, ν.toOuterMeasure {f | ∃ x : {v // v ∉ K}, f.1 x = a.1} =
        (Nat.card {v // v ∉ K} : ℝ≥0∞) / availableCount) := by
  classical
  intro availableCount
  intro
  let : Fintype (Candidates K A knownNames) := Fintype.ofFinite _
  let P : (V ↪ N) → Prop := fun f =>
    (∀ x : K, f x = knownNames x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A
  refine ⟨uniformPmf (Candidates K A knownNames), ?_, ?_, ?_⟩
  · intro f
    simp only [uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]
  · intro hs
    exact uniform_filter P hs
  · intro a
    let S : Set (Candidates K A knownNames) := {f | ∃ x : {v // v ∉ K}, f.1 x = a.1}
    let e := residualEmbedding K A knownNames hsep
    let : Fintype S := Fintype.ofFinite _
    change (uniformPmf (Candidates K A knownNames)).toOuterMeasure S =
      (Nat.card {v // v ∉ K} : ℝ≥0∞) / A.card
    rw [uniformPmf_toOuterMeasure_apply, ← Nat.card_eq_fintype_card (α := S),
      ← Nat.card_eq_fintype_card (α := Candidates K A knownNames)]
    have hA : A.card ≠ 0 := Finset.card_ne_zero.mpr ⟨a.1, a.2⟩
    have hC : Nat.card (Candidates K A knownNames) ≠ 0 := Finite.card_pos.ne'
    apply (ENNReal.div_eq_div_iff (Nat.cast_ne_zero.mpr hA) (ENNReal.natCast_ne_top _)
      (Nat.cast_ne_zero.mpr hC) (ENNReal.natCast_ne_top _)).mpr
    have hcount := card_embedding_hit_mul (X := {v // v ∉ K}) a
    rw [show Nat.card S = _ from Nat.card_congr (hitEquiv K A knownNames hsep a), Nat.card_congr e,
      Nat.card_eq_fintype_card (α := {v // v ∉ K}),
      Nat.card_eq_fintype_card (α := ({v // v ∉ K} ↪ A))]
    rw [Fintype.card_coe] at hcount
    exact_mod_cast (mul_comm _ _).trans (hcount.trans (mul_comm _ _))

end D5.S3.Combinatorics.Probability.PartialNameAssignment
