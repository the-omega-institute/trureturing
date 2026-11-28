/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseReduction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed SL(2,23) moves reduce the Paley weight bound to rows with anchored support. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pPaleyTripleNormalization
import OmegaBuild.Commands

/-!
# Anchoring sparse rows of the P48p Paley graph

A triple in the support is sent to infinity, zero and one. For a smaller
support, complete it to a triple and rotate the seed triple to place the
occupied directions at infinity or at infinity and zero. A global sign
fixes the infinity coefficient and preserves both Hamming weights.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseReduction

open scoped Matrix
open P48pFrameProjectiveAction (SL23 projectiveStep)
open P48pTernaryPaleyGraph (F3 paleyC)
open P48pPaleyAction (paleyPerm paleyRowAction paleyRowAction_ne_zero_iff paleyRowAction_mul
  paleyRowAction_vecMul hammingNorm_paleyRowAction)
open P48pPaleyTripleNormalization (exists_paleyPerm_image_triple)

open private directionEquiv paleyDirection from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph
open private paleyDirection_perm paleyPerm_one paleyPerm_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pPaleyAction

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- The occupied Paley directions in the order with infinity at index 23. -/
def rowSupport (a : Fin 24 → F3) : Finset (Fin 24) :=
  Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_rowSupport {a : Fin 24 → F3} {i : Fin 24} :
    i ∈ rowSupport a ↔ a i ≠ 0 := by
  simp [rowSupport]

private theorem rowSupport_action (g : SL23) (a : Fin 24 → F3) :
    rowSupport (paleyRowAction g a) = (rowSupport a).image (paleyPerm g) := by
  apply Finset.ext
  intro i
  obtain ⟨j, rfl⟩ := (paleyPerm g).surjective i
  rw [mem_rowSupport, paleyRowAction_ne_zero_iff]
  constructor
  · intro hj
    exact Finset.mem_image_of_mem _ (mem_rowSupport.mpr hj)
  · intro hi
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hi
    have heq : k = j := (paleyPerm g).injective hkj
    rw [heq] at hk
    exact mem_rowSupport.mp hk

private theorem rowSupport_neg (a : Fin 24 → F3) : rowSupport (-a) = rowSupport a := by
  apply Finset.ext
  intro i
  simp only [mem_rowSupport, Pi.neg_apply, neg_ne_zero]

private def seed : Finset (Fin 24) := {23, 0, 1}

private theorem seed_card : seed.card = 3 := by decide +kernel

private def seedCycle : SL23 :=
  ⟨!![1, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

private theorem seedCycle_zero : paleyPerm seedCycle 0 = 1 := by
  apply directionEquiv.injective
  change paleyDirection (paleyPerm seedCycle 0) = some 1
  exact (paleyDirection_perm seedCycle 0).trans (by
    change (projectiveStep seedCycle (some 0)).1 = some 1
    decide +kernel)

private theorem seedCycle_one : paleyPerm seedCycle 1 = 23 := by
  apply directionEquiv.injective
  change paleyDirection (paleyPerm seedCycle 1) = none
  exact (paleyDirection_perm seedCycle 1).trans (by
    change (projectiveStep seedCycle (some 1)).1 = none
    decide +kernel)

private theorem seedCycle_infinity : paleyPerm seedCycle 23 = 0 := by
  apply directionEquiv.injective
  change paleyDirection (paleyPerm seedCycle 23) = some 0
  exact (paleyDirection_perm seedCycle 23).trans (by
    change (projectiveStep seedCycle none).1 = some 0
    decide +kernel)

private theorem seed_rotation_to_one {i : Fin 24} (hi : i ∈ seed) :
    ∃ g : SL23, paleyPerm g i = 1 ∧ seed.image (paleyPerm g) = seed := by
  simp only [seed, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · refine ⟨seedCycle * seedCycle, ?_, ?_⟩
    · rw [paleyPerm_mul, seedCycle_infinity, seedCycle_zero]
    · simp only [seed, Finset.image_insert, Finset.image_singleton, paleyPerm_mul,
        seedCycle_zero, seedCycle_one, seedCycle_infinity] <;> decide +kernel
  · refine ⟨seedCycle, seedCycle_zero, ?_⟩
    simp only [seed, Finset.image_insert, Finset.image_singleton, seedCycle_zero,
      seedCycle_one, seedCycle_infinity] <;> decide +kernel
  · have hId : (paleyPerm 1 : Fin 24 → Fin 24) = id := funext paleyPerm_one
    exact ⟨1, paleyPerm_one 1, by rw [hId, Finset.image_id]⟩

private theorem seed_singleton_image {s : Finset (Fin 24)}
    (hs : s ⊆ seed) (hcard : s.card = 1) :
    ∃ g : SL23, s.image (paleyPerm g) = {23} := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨g, hg, _⟩ := seed_rotation_to_one (hs (Finset.mem_singleton_self i))
  exact ⟨g * seedCycle, by rw [Finset.image_singleton, paleyPerm_mul, hg, seedCycle_one]⟩

private theorem seed_pair_image {s : Finset (Fin 24)}
    (hs : s ⊆ seed) (hcard : s.card = 2) :
    ∃ g : SL23, s.image (paleyPerm g) = {23, 0} := by
  have hlt : s.card < seed.card := by rw [hcard, seed_card] <;> decide +kernel
  obtain ⟨i, hi, his⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hsub : s ⊆ seed.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun h => his (h ▸ hj), hs hj⟩
  have herase : s = seed.erase i := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_erase_of_mem hi, seed_card, hcard] <;> decide +kernel
  obtain ⟨g, hg, hseed⟩ := seed_rotation_to_one hi
  refine ⟨g, ?_⟩
  rw [herase, Finset.image_erase (paleyPerm g).injective, hseed, hg] <;> decide +kernel

private theorem exists_support_anchors (a : Fin 24 → F3) (ha : a ≠ 0) :
    ∃ g : SL23, 23 ∈ rowSupport (paleyRowAction g a) ∧
      (hammingNorm a = 1 → rowSupport (paleyRowAction g a) = {23}) ∧
      (hammingNorm a = 2 → rowSupport (paleyRowAction g a) = {23, 0}) ∧
      (3 ≤ hammingNorm a → 0 ∈ rowSupport (paleyRowAction g a) ∧
        1 ∈ rowSupport (paleyRowAction g a)) := by
  by_cases hlarge : 3 ≤ hammingNorm a
  · obtain ⟨t, hts, hcard⟩ :=
      Finset.exists_subset_card_eq (s := rowSupport a) hlarge
    obtain ⟨g, hg⟩ := exists_paleyPerm_image_triple t hcard
    have hseed : seed ⊆ rowSupport (paleyRowAction g a) := by
      change ({23, 0, 1} : Finset (Fin 24)) ⊆ rowSupport (paleyRowAction g a)
      rw [← hg, rowSupport_action]
      exact Finset.image_subset_image hts
    refine ⟨g, hseed (by decide +kernel : (23 : Fin 24) ∈ seed), ?_, ?_, ?_⟩
    · intro h
      omega
    · intro h
      omega
    · intro _
      exact ⟨hseed (by decide +kernel : (0 : Fin 24) ∈ seed),
        hseed (by decide +kernel : (1 : Fin 24) ∈ seed)⟩
  · have hle : (rowSupport a).card ≤ 3 := by
      change hammingNorm a ≤ 3
      omega
    obtain ⟨t, hst, hcard⟩ := Finset.exists_superset_card_eq hle
      (by decide +kernel : 3 ≤ Fintype.card (Fin 24))
    obtain ⟨g, hg⟩ := exists_paleyPerm_image_triple t hcard
    let s := rowSupport (paleyRowAction g a)
    have hseed : s ⊆ seed := by
      change rowSupport (paleyRowAction g a) ⊆ ({23, 0, 1} : Finset (Fin 24))
      rw [rowSupport_action, ← hg]
      exact Finset.image_subset_image hst
    have hsCard : s.card = hammingNorm a := hammingNorm_paleyRowAction g a
    have hpos : 0 < hammingNorm a := hammingNorm_pos_iff.mpr ha
    obtain ⟨r, hr⟩ : ∃ r : SL23, s.image (paleyPerm r) =
        (if hammingNorm a = 1 then {23} else {23, 0}) := by
      by_cases hone : hammingNorm a = 1
      · rw [if_pos hone]
        exact seed_singleton_image hseed (hsCard.trans hone)
      · rw [if_neg hone]
        have htwo : hammingNorm a = 2 := by omega
        exact seed_pair_image hseed (hsCard.trans htwo)
    have hsupport : rowSupport (paleyRowAction (g * r) a) =
        (if hammingNorm a = 1 then {23} else {23, 0}) := by
      rw [paleyRowAction_mul, rowSupport_action]
      exact hr
    refine ⟨g * r, ?_, ?_, ?_, ?_⟩
    · rw [hsupport]
      split <;> decide +kernel
    · intro h
      simpa only [if_pos h] using hsupport
    · intro h
      have hne : hammingNorm a ≠ 1 := by omega
      simpa only [if_neg hne] using hsupport
    · intro h
      omega

private theorem ternary_sign {x : F3} (hx : x ≠ 0) : x = 1 ∨ x = -1 :=
  (by decide +kernel : ∀ t : F3, t ≠ 0 → t = 1 ∨ t = -1) x hx

private theorem exists_sign_normalized (a : Fin 24 → F3) (ha : a 23 ≠ 0) :
    ∃ b : Fin 24 → F3, (b = a ∨ b = -a) ∧ b 23 = 1 := by
  rcases ternary_sign ha with h | h
  · exact ⟨a, Or.inl rfl, h⟩
  · exact ⟨-a, Or.inr rfl, by simp only [Pi.neg_apply, h, neg_neg]⟩

/-- The support and coefficients required of the input to an anchored check. -/
def HasAnchoredSupport (a : Fin 24 → F3) : Prop :=
  a 23 = 1 ∧
    (hammingNorm a = 1 → rowSupport a = {23}) ∧
    (hammingNorm a = 2 → rowSupport a = {23, 0}) ∧
    (3 ≤ hammingNorm a → a 0 ≠ 0 ∧ a 1 ≠ 0)

/-- An actual projective move and an optional global sign give an anchored
row with the same input and output weights. -/
theorem exists_anchored_paleyRow (a : Fin 24 → F3) (ha : a ≠ 0) :
    ∃ (g : SL23) (b : Fin 24 → F3),
      (b = paleyRowAction g a ∨ b = -paleyRowAction g a) ∧
      hammingNorm b = hammingNorm a ∧
      hammingNorm (b ᵥ* paleyC) = hammingNorm (a ᵥ* paleyC) ∧
      HasAnchoredSupport b := by
  obtain ⟨g, hinf, hone, htwo, hthree⟩ := exists_support_anchors a ha
  obtain ⟨b, hb, hb23⟩ := exists_sign_normalized (paleyRowAction g a) (mem_rowSupport.mp hinf)
  have hs : rowSupport b = rowSupport (paleyRowAction g a) := by
    rcases hb with h | h
    · rw [h]
    · rw [h, rowSupport_neg]
  have hw : hammingNorm b = hammingNorm a :=
    (congrArg Finset.card hs).trans (hammingNorm_paleyRowAction g a)
  have hgraph : hammingNorm (paleyRowAction g a ᵥ* paleyC) =
      hammingNorm (a ᵥ* paleyC) := by
    rw [← paleyRowAction_vecMul, hammingNorm_paleyRowAction]
  have hout : hammingNorm (b ᵥ* paleyC) = hammingNorm (a ᵥ* paleyC) := by
    rcases hb with h | h
    · rw [h]
      exact hgraph
    · rw [h, Matrix.neg_vecMul]
      exact (congrArg Finset.card (rowSupport_neg (paleyRowAction g a ᵥ* paleyC))).trans hgraph
  refine ⟨g, b, hb, hw, hout, ?_⟩
  refine ⟨hb23, ?_, ?_, ?_⟩
  · intro h
    rw [hw] at h
    exact hs.trans (hone h)
  · intro h
    rw [hw] at h
    exact hs.trans (htwo h)
  · intro h
    rw [hw] at h
    obtain ⟨h0, h1⟩ := hthree h
    rw [← hs] at h0 h1
    exact ⟨mem_rowSupport.mp h0, mem_rowSupport.mp h1⟩

/-- The sparse weight bound is equivalent to its restriction to the exact
anchored support shapes. -/
theorem paley_small_support_bound_iff_anchored :
    (∀ a : Fin 24 → F3, a ≠ 0 → hammingNorm a ≤ 6 →
      12 < hammingNorm a + hammingNorm (a ᵥ* paleyC)) ↔
    (∀ b : Fin 24 → F3, HasAnchoredSupport b → hammingNorm b ≤ 6 →
      12 < hammingNorm b + hammingNorm (b ᵥ* paleyC)) := by
  constructor
  · intro h b hb hle
    have hne : b ≠ 0 := by
      intro hz
      have h23 : b 23 = 1 := hb.1
      rw [hz] at h23
      exact zero_ne_one h23
    exact h b hne hle
  · intro h a ha hle
    obtain ⟨_, b, _, hw, hout, hb⟩ := exists_anchored_paleyRow a ha
    have hle' : hammingNorm b ≤ 6 := by rwa [hw]
    have hbound := h b hb hle'
    rwa [hw, hout] at hbound

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseReduction
