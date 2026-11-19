/- GID: D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers
   mirror-E: none(waiver:finite-group-fiber-identities)
   anchors: []
   utility: none
   digest: Exact generating-pair fiber counts and the nonabelian square-root deficit. -/

import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.Real.Irrational

/-! Generating-pair partitions, prime-order fibers and the nonabelian deficit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

namespace D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers

noncomputable section

variable {G : Type} [Group G] [Fintype G]
attribute [local instance] CyclicExtensionRefutation.subgroupFintype

/-- All ordered and repeated pairs whose generated subgroup is exactly H. -/
def generatingPairs (H : Subgroup G) : Finset (G × G) := by
  classical
  exact Finset.univ.filter (fun p => Subgroup.closure ({p.1, p.2} : Set G) = H)

/-- The size of the literal pair fiber over H. -/
def pairCount (H : Subgroup G) : ℕ := (generatingPairs H).card

private theorem mem_generatingPairs (H : Subgroup G) (p : G × G) :
    p ∈ generatingPairs H ↔ Subgroup.closure ({p.1, p.2} : Set G) = H := by
  classical
  simp [generatingPairs]

private theorem closure_pair_swap (a b : G) :
    Subgroup.closure ({a,b} : Set G) = Subgroup.closure ({b,a} : Set G) := by
  rw [Set.pair_comm]

private theorem closure_pair_mul (a b : G) :
    Subgroup.closure ({a,a*b} : Set G) = Subgroup.closure ({a,b} : Set G) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Subgroup.subset_closure (by simp),
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))⟩
  · apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨Subgroup.subset_closure (by simp),?_⟩
    have ha : a ∈ Subgroup.closure ({a,a*b} : Set G) := Subgroup.subset_closure (by simp)
    have hab : a*b ∈ Subgroup.closure ({a,a*b} : Set G) := Subgroup.subset_closure (by simp)
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hab

private theorem closure_mul_pair (a b : G) :
    Subgroup.closure ({a*b,b} : Set G) = Subgroup.closure ({a,b} : Set G) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)), Subgroup.subset_closure (by simp)⟩
  · apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨?_,Subgroup.subset_closure (by simp)⟩
    have hb : b ∈ Subgroup.closure ({a*b,b} : Set G) := Subgroup.subset_closure (by simp)
    have hab : a*b ∈ Subgroup.closure ({a*b,b} : Set G) := Subgroup.subset_closure (by simp)
    simpa using Subgroup.mul_mem _ hab (Subgroup.inv_mem _ hb)

private theorem six_pairs_le (a b : G) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    6 ≤ pairCount (Subgroup.closure ({a,b} : Set G)) := by
  classical
  have hx : a*b ≠ a := by simpa using hb
  have hy : a*b ≠ b := by simpa using ha
  let s : Finset (G × G) := {(a,b),(b,a),(a,a*b),(a*b,a),(b,a*b),(a*b,b)}
  have hs : s.card = 6 := by
    simp [s, ha, hb, hab, hab.symm, hx, hx.symm, hy, hy.symm]
  rw [← hs]
  apply Finset.card_le_card
  intro p hp
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (mem_generatingPairs _ _).mpr rfl
  · exact (mem_generatingPairs _ _).mpr (closure_pair_swap _ _)
  · exact (mem_generatingPairs _ _).mpr (closure_pair_mul _ _)
  · exact (mem_generatingPairs _ _).mpr ((closure_pair_swap _ _).trans (closure_pair_mul _ _))
  · exact (mem_generatingPairs _ _).mpr ((closure_pair_swap _ _).trans (closure_mul_pair _ _))
  · exact (mem_generatingPairs _ _).mpr (closure_mul_pair _ _)

/-- The trivial subgroup retains precisely the ordered identity pair. -/
theorem pairCount_bot : pairCount (⊥ : Subgroup G) = 1 := by
  classical
  have h : generatingPairs (⊥ : Subgroup G) = {(1,1)} := by
    ext p
    simp [generatingPairs, Subgroup.closure_eq_bot_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff, Prod.ext_iff]
  simp [pairCount, h]

/-- Every nontrivial realized subgroup fiber has at least three ordered generators. -/
theorem pairCount_ge_three (H : Subgroup G) (hH : H ≠ ⊥) (hr : 0 < pairCount H) :
    3 ≤ pairCount H := by
  classical
  obtain ⟨⟨a,b⟩, hp⟩ := Finset.card_pos.mp hr
  have hgen := (mem_generatingPairs H (a,b)).mp hp
  have hnon : a ≠ 1 ∨ b ≠ 1 := by
    by_contra h
    push Not at h
    apply hH
    rw [← hgen, h.1, h.2]
    simp
  by_cases ha : a = 1
  · have hb : b ≠ 1 := hnon.resolve_left (by simpa using ha)

    have hs : ({(1,b),(b,1),(b,b)} : Finset (G × G)).card = 3 := by simp [hb, Ne.symm hb]
    rw [← hs]
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> apply (mem_generatingPairs H _).mpr
    · simpa [ha, Subgroup.closure_insert_one] using hgen
    · simpa [ha, Set.pair_comm, Subgroup.closure_insert_one] using hgen
    · simpa [ha, Subgroup.closure_insert_one] using hgen
  · by_cases hb : b = 1
    · have hs : ({(1,a),(a,1),(a,a)} : Finset (G × G)).card = 3 := by simp [ha, Ne.symm ha]
      rw [← hs]
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> apply (mem_generatingPairs H _).mpr
      · simpa [hb, Set.pair_comm, Subgroup.closure_insert_one] using hgen
      · simpa [hb, Set.pair_comm, Subgroup.closure_insert_one] using hgen
      · simpa [hb, Set.pair_comm, Subgroup.closure_insert_one] using hgen
    · by_cases hab : a = b
      · have hs : ({(1,a),(a,1),(a,a)} : Finset (G × G)).card = 3 := by simp [ha, Ne.symm ha]
        rw [← hs]
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> apply (mem_generatingPairs H _).mpr
        · simpa [← hab, Set.pair_comm, Subgroup.closure_insert_one] using hgen
        · simpa [← hab, Set.pair_comm, Subgroup.closure_insert_one] using hgen
        · simpa [← hab, Set.pair_comm, Subgroup.closure_insert_one] using hgen
      · rw [← hgen]
        exact (by omega : 3 ≤ 6).trans (six_pairs_le a b ha hb hab)

/-- A noncommuting pair gives a realized subgroup fiber of size at least six. -/
theorem exists_large_fiber (hn : ∃ a b : G, a*b ≠ b*a) :
    ∃ H : Subgroup G, 6 ≤ pairCount H := by
  rcases hn with ⟨a,b,hab⟩
  refine ⟨Subgroup.closure ({a,b} : Set G), six_pairs_le a b ?_ ?_ ?_⟩
  · intro ha; apply hab; simp [ha]
  · intro hb; apply hab; simp [hb]
  · intro he; apply hab; simp [he]

/-- Summing all fibers counts every ordered pair once. -/
theorem sum_pairCount : ∑ H : Subgroup G, pairCount H = Fintype.card G ^ 2 := by
  classical
  simpa [pairCount, generatingPairs, Fintype.card_prod, pow_two] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (G × G))
      (Finset.univ : Finset (Subgroup G))
      (fun p => Subgroup.closure ({p.1,p.2} : Set G))

private theorem generates_prime_iff (H : Subgroup G) (hp : (Nat.card H).Prime) (a b : G) :
    Subgroup.closure ({a,b} : Set G) = H ↔ a ∈ H ∧ b ∈ H ∧ (a ≠ 1 ∨ b ≠ 1) := by
  constructor
  · intro h
    have ha : a ∈ H := h ▸ Subgroup.subset_closure (by simp)
    have hb : b ∈ H := h ▸ Subgroup.subset_closure (by simp)
    refine ⟨ha,hb,?_⟩
    by_contra hn
    push Not at hn
    have hbH : H = ⊥ := by rw [← h, hn.1, hn.2]; simp
    have hc : Nat.card H = 1 := by rw [hbH]; simp
    exact hp.ne_one hc
  · rintro ⟨ha,hb,hn⟩
    let K := Subgroup.closure ({a,b} : Set G)
    have hk : K ≤ H := by
      change Subgroup.closure ({a,b} : Set G) ≤ H
      apply (Subgroup.closure_le H).mpr
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using And.intro ha hb
    letI : Fact (Nat.card H).Prime := ⟨hp⟩
    rcases (K.subgroupOf H).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · have heq : K = ⊥ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hk, hbot, Subgroup.map_bot]
      have haK : a ∈ K := Subgroup.subset_closure (by simp)
      have hbK : b ∈ K := Subgroup.subset_closure (by simp)
      rw [heq] at haK hbK
      have ha1 : a = 1 := haK
      have hb1 : b = 1 := hbK
      exact False.elim (hn.elim (fun h => h ha1) (fun h => h hb1))
    · exact le_antisymm hk (Subgroup.subgroupOf_eq_top.mp htop)

/-- In a prime-order subgroup, every pair except the identity pair generates it. -/
theorem pairCount_prime (H : Subgroup G) (hp : (Nat.card H).Prime) :
    pairCount H = Nat.card H ^ 2 - 1 := by
  classical
  let f : H × H → G × G := fun p => (p.1.1,p.2.1)
  have hf : Function.Injective f := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hs : generatingPairs H = (Finset.univ.erase (1,1)).image f := by
    ext p
    rw [mem_generatingPairs, generates_prime_iff H hp]
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨ha,hb,hn⟩
      refine ⟨(⟨p.1,ha⟩,⟨p.2,hb⟩),?_,rfl⟩
      intro he
      have ha1 : p.1 = 1 := congrArg (fun q : H × H => (q.1 : G)) he
      have hb1 : p.2 = 1 := congrArg (fun q : H × H => (q.2 : G)) he
      exact hn.elim (fun h => h ha1) (fun h => h hb1)
    · rintro ⟨q,hq,rfl⟩
      refine ⟨q.1.2,q.2.2,?_⟩
      by_contra hn
      push Not at hn
      exact hq (Prod.ext (Subtype.ext hn.1) (Subtype.ext hn.2))
  simp [pairCount, hs, Finset.card_image_of_injective _ hf, Nat.card_eq_fintype_card,
    Fintype.card_prod, pow_two]

/-- Cauchy's theorem produces a nonsquare generating-pair fiber in every nontrivial group. -/
theorem exists_prime_fiber (hG : 1 < Fintype.card G) :
    ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ Nat.card H = p ∧ pairCount H = p^2-1 := by
  obtain ⟨p,hp,hdvd⟩ := Nat.exists_prime_and_dvd (by omega : Fintype.card G ≠ 1)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card (G := G) p hdvd
  have hcard : Nat.card (Subgroup.zpowers a) = p := (Nat.card_zpowers a).trans ha
  refine ⟨p,Subgroup.zpowers a,hp,hcard,?_⟩
  rw [pairCount_prime _ (hcard ▸ hp), hcard]


/-- The realized subgroup fibers; zero fibers remain in the vertex carrier. -/
def positiveFibers : Finset (Subgroup G) := by
  classical
  exact Finset.univ.filter (fun H => 0 < pairCount H)

/-- The six-pair fiber pays for the identity star in the adjacency square-root sum. -/
theorem sqrt_sum_le_deficit (hn : ∃ a b : G, a*b ≠ b*a) :
    (∑ H : Subgroup G, Real.sqrt (pairCount H)) ≤
      (Fintype.card G : ℝ)^2 - (positiveFibers (G := G)).card := by
  classical
  obtain ⟨K,hK⟩ := exists_large_fiber hn
  have hKbot : K ≠ ⊥ := by intro he; rw [he,pairCount_bot] at hK; omega
  have hbound (H : Subgroup G) : Real.sqrt (pairCount H) ≤
      (pairCount H : ℝ) - (if pairCount H = 0 then 0 else 1) +
        (if H = ⊥ then 1 else 0) - (if H = K then 1 else 0) := by
    by_cases hbot : H = ⊥
    · subst H
      simp [pairCount_bot,hKbot.symm]
    · by_cases he : H = K
      · subst H
        have hr : (6 : ℝ) ≤ pairCount K := by exact_mod_cast hK
        have hs : Real.sqrt (pairCount K) ≤ (pairCount K : ℝ)-2 := by
          apply (Real.sqrt_le_left (by linarith)).mpr
          nlinarith
        simpa [hbot,show pairCount K ≠ 0 by omega, sub_sub] using (show Real.sqrt (pairCount K) ≤ (pairCount K : ℝ) - (1+1) by linarith)
      · by_cases hz : pairCount H = 0
        · simp [hz,hbot,he]
        · have h3 := pairCount_ge_three H hbot (Nat.pos_of_ne_zero hz)
          have hr : (3 : ℝ) ≤ pairCount H := by exact_mod_cast h3
          have hs : Real.sqrt (pairCount H) ≤ (pairCount H : ℝ)-1 := by
            apply (Real.sqrt_le_left (by linarith)).mpr
            nlinarith
          simpa [hz,hbot,he] using hs
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Subgroup G)))
    (fun H _ => hbound H)
  have hc : (∑ H : Subgroup G, (if pairCount H = 0 then (0 : ℝ) else 1)) =
      (positiveFibers (G := G)).card := by
    simpa only [positiveFibers, Nat.pos_iff_ne_zero, ite_not] using
      (Finset.sum_boole (R := ℝ) (fun H : Subgroup G => pairCount H ≠ 0) Finset.univ)
  have hm : (∑ H : Subgroup G, (pairCount H : ℝ)) = (Fintype.card G : ℝ)^2 := by
    exact_mod_cast (sum_pairCount (G := G))
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hm, hc,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, add_sub_cancel_right] using hs

end
end D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
