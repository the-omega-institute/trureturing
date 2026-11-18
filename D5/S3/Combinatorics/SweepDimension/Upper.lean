/- GID: D5/S3/Combinatorics/SweepDimension/Upper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SweepDimension/Upper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Extension.Linear]
   utility: none
   digest: A finite poset has a sweep system of exactly its three-chain-free maximum size. -/

import D5.S3.Combinatorics.SweepDimension.Basic
import D5.S3.Combinatorics.SweepDimension.FiniteDilworth
import Mathlib.Order.Extension.Linear
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SweepDimension.Upper

open Basic

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- The defining maximum bounds every three-chain-free subset. -/
theorem card_le_theta {S : Finset α} (hS : ThreeChainFree S) :
    S.card ≤ theta (α := α) := by
  classical
  unfold theta
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hS⟩, rfl⟩

private theorem product_antichain_projection {S : Finset (α × Fin 2)}
    (hS : IsAntichain (· ≤ ·) (S : Set (α × Fin 2))) :
    (S.image Prod.fst).card = S.card ∧ ThreeChainFree (S.image Prod.fst) := by
  classical
  constructor
  · apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    by_contra hne
    have hab' : a.1 = b.1 := hab
    rcases le_total a.2 b.2 with h | h
    · exact hS ha hb hne ⟨hab'.le, h⟩
    · exact hS hb ha (Ne.symm hne) ⟨hab'.symm.le, h⟩
  · intro a b c ha hb hc hchain
    obtain ⟨⟨a', i⟩, hai, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨b', j⟩, hbj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨⟨c', k⟩, hck, rfl⟩ := Finset.mem_image.mp hc
    have hij : ¬i ≤ j := by
      intro h
      apply hS hai hbj _ ⟨hchain.1.le, h⟩
      intro e
      exact hchain.1.ne (congrArg Prod.fst e)
    have hjk : ¬j ≤ k := by
      intro h
      apply hS hbj hck _ ⟨hchain.2.le, h⟩
      intro e
      exact hchain.2.ne (congrArg Prod.fst e)
    omega

private theorem product_width_le_theta :
    FiniteDilworth.maxAntichainSize (α × Fin 2) ≤ theta (α := α) := by
  classical
  obtain ⟨S, hS, hcard⟩ :=
    FiniteDilworth.exists_isAntichain_card_eq_maxAntichainSize (α := α × Fin 2)
  obtain ⟨hproj, hfree⟩ := product_antichain_projection hS
  have := card_le_theta hfree
  omega

/-- Three ordered blocks: the first reversed, the second forward, then the rest. -/
private def blockRel (A B : Set α) (x y : α) : Prop :=
  x = y ∨ (x ∈ A ∧ (y ∉ A ∨ y ≤ x)) ∨
    (x ∉ A ∧ x ∈ B ∧ y ∉ A ∧ (y ∉ B ∨ x ≤ y))

private theorem block_partial (A B : Set α) : IsPartialOrder α (blockRel A B) where
  refl x := Or.inl rfl
  antisymm a b hab hba := by
    grind only [blockRel, le_antisymm]
  trans a b c hab hbc := by
    rcases hab with rfl | ⟨ha, hab⟩ | ⟨ha, haB, hbA, hab⟩
    · exact hbc
    · rcases hbc with rfl | ⟨hb, hbc⟩ | ⟨hb, _, hcA, _⟩
      · exact Or.inr (Or.inl ⟨ha, hab⟩)
      · have hba : b ≤ a := hab.resolve_left (not_not.mpr hb)
        exact Or.inr (Or.inl ⟨ha, hbc.imp id (fun h => h.trans hba)⟩)
      · exact Or.inr (Or.inl ⟨ha, Or.inl hcA⟩)
    · rcases hbc with rfl | ⟨hb, _⟩ | ⟨hb, hbB, hcA, hbc⟩
      · exact Or.inr (Or.inr ⟨ha, haB, hbA, hab⟩)
      · exact (hbA hb).elim
      · have hab' : a ≤ b := hab.resolve_left (not_not.mpr hbB)
        exact Or.inr (Or.inr ⟨ha, haB, hcA, hbc.imp id (fun h => hab'.trans h)⟩)

private theorem chain_order (D : Finset (α × Fin 2))
    (hD : IsChain (· ≤ ·) (D : Set (α × Fin 2))) :
    ∃ o : LinearOrderRel (α := α),
      (∀ y, (y, 0) ∈ D → ∀ x, ¬y < x → o.rel y x) ∧
      (∀ y, (y, 1) ∈ D → ∀ x, ¬x < y → o.rel y x) := by
  classical
  let A : Set α := {x | (x, 0) ∈ D}
  let B : Set α := {x | (x, 1) ∈ D}
  letI : IsPartialOrder α (blockRel A B) := block_partial A B
  obtain ⟨r, hr, hext⟩ := extend_partialOrder (blockRel A B)
  refine ⟨⟨r, hr⟩, ?_, ?_⟩
  · intro y hy x hnot
    apply hext
    refine Or.inr (Or.inl ⟨hy, ?_⟩)
    by_cases hx : x ∈ A
    · right
      rcases hD.total (show (y, 0) ∈ (D : Set (α × Fin 2)) from hy)
          (show (x, 0) ∈ (D : Set (α × Fin 2)) from hx) with hc | hc
      · exact ((lt_or_eq_of_le hc.1).resolve_left hnot).symm.le
      · exact hc.1
    · exact Or.inl hx
  · intro y hy x hnot
    apply hext
    by_cases hyA : y ∈ A
    · refine Or.inr (Or.inl ⟨hyA, ?_⟩)
      by_cases hx : x ∈ A
      · right
        have hc := hD.total (show (x, 0) ∈ (D : Set (α × Fin 2)) from hx)
          (show (y, 1) ∈ (D : Set (α × Fin 2)) from hy)
        rcases hc with hc | hc
        · exact hc.1
        · have : (1 : Fin 2) ≤ 0 := hc.2
          omega
      · exact Or.inl hx
    · by_cases hxA : x ∈ A
      · have hxy : x ≤ y := by
          rcases hD.total (show (x, 0) ∈ (D : Set (α × Fin 2)) from hxA)
            (show (y, 1) ∈ (D : Set (α × Fin 2)) from hy) with h | h
          · exact h.1
          · have : (1 : Fin 2) ≤ 0 := h.2
            omega
        have heq : x = y := (lt_or_eq_of_le hxy).resolve_left hnot
        exact (hyA (heq ▸ hxA)).elim
      · refine Or.inr (Or.inr ⟨hyA, hy, hxA, ?_⟩)
        by_cases hxB : x ∈ B
        · right
          rcases hD.total (show (y, 1) ∈ (D : Set (α × Fin 2)) from hy)
            (show (x, 1) ∈ (D : Set (α × Fin 2)) from hxB) with h | h
          · exact h.1
          · exact ((lt_or_eq_of_le h.1).resolve_left hnot).symm.le
        · exact Or.inl hxB

/-- A sweep system exists with exactly `theta` carried linear orders. -/
theorem exists_sweep_theta :
    ∃ orders : Fin (theta (α := α)) → LinearOrderRel (α := α),
      IsSweepSystem (theta (α := α)) orders := by
  classical
  obtain ⟨C, hchain, hcover, hcard⟩ :=
    FiniteDilworth.exists_chain_cover (α := α × Fin 2)
  have hcθ : C.card ≤ theta (α := α) := hcard.trans product_width_le_theta
  choose orders horders using fun d : C => chain_order d.1 (hchain d.1 d.2)
  let k := C.card
  let e : Fin k ≃ C := by
    simpa only [k, Fintype.card_coe] using (Fintype.equivFin C).symm
  let os : Fin k → LinearOrderRel (α := α) := fun i => orders (e i)
  have hsweep : IsSweepSystem k os := by
    intro I hI y hy
    by_cases htop : ∃ z ∈ I, y < z
    · obtain ⟨z, hz, hyz⟩ := htop
      obtain ⟨d, hd, hyd⟩ := hcover (y, 1)
      refine ⟨e.symm ⟨d, hd⟩, ?_⟩
      intro x hx
      simp only [os, Equiv.apply_symm_apply]
      apply (horders ⟨d, hd⟩).2 y hyd x
      intro hxy
      exact hy (hI hx hz hxy.le hyz.le)
    · obtain ⟨d, hd, hyd⟩ := hcover (y, 0)
      refine ⟨e.symm ⟨d, hd⟩, ?_⟩
      intro x hx
      simp only [os, Equiv.apply_symm_apply]
      apply (horders ⟨d, hd⟩).1 y hyd x
      intro hyx
      exact htop ⟨x, hx, hyx⟩
  have hθk : theta (α := α) ≤ k := theta_le_of_sweep os hsweep
  have heq : k = theta (α := α) := le_antisymm hcθ hθk
  exact heq ▸ ⟨os, hsweep⟩

/-- Sweep dimension is the least number of orders satisfying the source sweep condition. -/
noncomputable def sweepDimension : ℕ := by
  classical
  exact Nat.find (show ∃ k, ∃ orders : Fin k → LinearOrderRel (α := α),
    IsSweepSystem k orders from ⟨theta (α := α), exists_sweep_theta⟩)

/-- The universal finite-poset identity, including the empty and singleton cases. -/
theorem sweepDimension_eq_theta : sweepDimension (α := α) = theta (α := α) := by
  classical
  apply le_antisymm
  · exact Nat.find_min' _ exists_sweep_theta
  · obtain ⟨orders, horders⟩ := Nat.find_spec
      (show ∃ k, ∃ orders : Fin k → LinearOrderRel (α := α),
        IsSweepSystem k orders from ⟨theta (α := α), exists_sweep_theta⟩)
    exact theta_le_of_sweep orders horders

end D5.S3.Combinatorics.SweepDimension.Upper
