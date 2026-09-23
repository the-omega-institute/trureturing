/- GID: D5/S3/Combinatorics/Graph/DUFStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Common links and exact neighborhood fibers of disjoint-union-free triple families. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFStructure

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All unordered pairs of vertices, including pairs absent from the triple family. -/
def pairs : Finset (Finset V) := univ.powersetCard 2

/-- The literal uniqueness of an unordered pair of disjoint members from its union. -/
def DUF (H : Finset (Finset V)) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, ∀ C ∈ H, ∀ D ∈ H,
    Disjoint A B → Disjoint C D → A ∪ B = C ∪ D →
      (A = C ∧ B = D) ∨ (A = D ∧ B = C)

/-- The exact set of extensions of a pair to a triple. -/
def neighbors (H : Finset (Finset V)) (p : Finset V) : Finset V :=
  univ.filter fun x => x ∉ p ∧ insert x p ∈ H

/-- Transposing the directed extension relation gives the common-link pair family. -/
def common (H : Finset (Finset V)) (q : Finset V) : Finset (Finset V) :=
  pairs.filter fun p => q ⊆ neighbors H p

/-- Pairs with exactly the prescribed neighborhood. -/
def fiber (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  pairs.filter fun p => neighbors H p = S

/-- The pair-codegree hypothesis ranges over all ground-set pairs. -/
def CapFour (H : Finset (Finset V)) : Prop :=
  ∀ p ∈ (pairs : Finset (Finset V)), (neighbors H p).card ≤ 4

/-- Edges of a star, with its center and leaves specified separately. -/
def star (c : V) (A : Finset V) : Finset (Finset V) := A.image fun a => {c, a}

/-- Pairwise intersection for a family of edges. -/
def Intersecting (F : Finset (Finset V)) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, ¬ Disjoint p q

/-- An intersecting nonempty pair family has a common vertex or is a triangle. -/
theorem intersecting_classification (F : Finset (Finset V))
    (hp : ∀ p ∈ F, p.card = 2) (hi : Intersecting F) (hne : F.Nonempty) :
    (∃ c A, c ∉ A ∧ F = star c A ∧ A.card = F.card) ∨
      ∃ T : Finset V, T.card = 3 ∧ F = T.powersetCard 2 := by
  have mkstar (c : V) (hc : ∀ p ∈ F, c ∈ p) :
      ∃ A, c ∉ A ∧ F = star c A ∧ A.card = F.card := by
    let A := F.biUnion fun p => p.erase c
    have hcA : c ∉ A := by simp [A]
    have hF : F = star c A := by
      ext e
      constructor
      · intro he
        obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (hp e he)
        have hce := hc _ he
        simp only [mem_insert, mem_singleton] at hce
        rcases hce with rfl | rfl
        · exact mem_image.mpr ⟨y, mem_biUnion.mpr ⟨_, he, by simp [hxy.symm]⟩, rfl⟩
        · exact mem_image.mpr ⟨x, mem_biUnion.mpr ⟨_, he, by simp [hxy]⟩,
            by ext; simp [or_comm]⟩
      · intro he
        obtain ⟨x, hx, rfl⟩ := mem_image.mp he
        obtain ⟨p, hpF, hxp⟩ := mem_biUnion.mp hx
        have hcp := hc _ hpF
        have heq : p = {c, x} := by
          apply (eq_of_subset_of_card_le (by
            simpa only [insert_subset_iff, singleton_subset_iff] using
              And.intro hcp (mem_erase.mp hxp).2) ?_).symm
          simpa [Ne.symm (mem_erase.mp hxp).1] using (hp p hpF).le
        simpa [heq] using hpF
    refine ⟨A, hcA, hF, ?_⟩
    rw [hF, star, card_image_iff.mpr]
    intro a ha b hb he
    have ha' : a ≠ c := by intro he; subst a; exact hcA ha
    have : a ∈ ({c, b} : Finset V) := by
      change ({c, a} : Finset V) = {c, b} at he
      rw [← he]; simp
    simpa [ha'] using this
  obtain ⟨p, hpF⟩ := hne
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (hp p hpF)
  by_cases ha : ∀ p ∈ F, a ∈ p
  · exact Or.inl ⟨a, mkstar a ha⟩
  push Not at ha
  obtain ⟨q, hqF, haq⟩ := ha
  have hbq : b ∈ q := by
    have := hi {a, b} hpF q hqF
    simpa [disjoint_left, haq] using this
  obtain ⟨c, hbc, hq⟩ : ∃ c, b ≠ c ∧ q = {b, c} := by
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (hp q hqF)
    simp only [mem_insert, mem_singleton] at hbq
    rcases hbq with rfl | rfl
    · exact ⟨y, hxy, rfl⟩
    · exact ⟨x, hxy.symm, by ext; simp [or_comm]⟩
  subst q
  have hac : a ≠ c := by simpa [hab] using haq
  by_cases hb : ∀ p ∈ F, b ∈ p
  · exact Or.inl ⟨b, mkstar b hb⟩
  push Not at hb
  obtain ⟨r, hrF, hbr⟩ := hb
  have har : a ∈ r := by
    have := hi {a, b} hpF r hrF
    simpa [disjoint_left, hbr] using this
  have hcr : c ∈ r := by
    have := hi {b, c} hqF r hrF
    simpa [disjoint_left, hbr] using this
  have hr : r = {a, c} := by
    apply (eq_of_subset_of_card_le (by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro har hcr) ?_).symm
    simpa [hac] using (hp r hrF).le
  subst r
  right
  refine ⟨{a, b, c}, by simp [hab, hac, hbc], ?_⟩
  ext e
  constructor
  · intro he
    refine mem_powersetCard.mpr ⟨?_, hp e he⟩
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (hp e he)
    have h1 := hi {a, b} hpF {x, y} he
    have h2 := hi {b, c} hqF {x, y} he
    have h3 := hi {a, c} hrF {x, y} he
    simp only [disjoint_left, mem_insert, mem_singleton] at h1 h2 h3
    simp only [insert_subset_iff, singleton_subset_iff, mem_insert, mem_singleton]
    grind
  · intro he
    obtain ⟨hes, hec⟩ := mem_powersetCard.mp he
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hec
    simp only [insert_subset_iff, singleton_subset_iff, mem_insert, mem_singleton] at hes
    rcases hes with ⟨hx, hy⟩
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [pair_comm]

/-- Two disjoint common-link edges would give two different decompositions into triples. -/
theorem common_intersecting (H : Finset (Finset V)) (hd : DUF H)
    (q : Finset V) (hq : q.card = 2) : Intersecting (common H q) := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hq
  intro p hp r hr hpr
  simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
    insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ] at hp hr
  obtain ⟨hp2, ⟨hup, hHp⟩, ⟨hvp, hVp⟩⟩ := hp
  obtain ⟨hr2, ⟨hur, hHr⟩, ⟨hvr, hVr⟩⟩ := hr
  have hd1 : Disjoint (insert u p) (insert v r) := by
    simp [disjoint_insert_left, disjoint_insert_right, hpr, hur, hvp, huv.symm]
  have hd2 : Disjoint (insert v p) (insert u r) := by
    simp [disjoint_insert_left, disjoint_insert_right, hpr, hup, hvr, huv]
  have he : insert u p ∪ insert v r = insert v p ∪ insert u r := by
    ext x
    simp only [mem_union, mem_insert]
    tauto
  rcases hd _ hHp _ hVr _ hVp _ hHr hd1 hd2 he with h | h
  · have : u ∈ insert v p := h.1 ▸ mem_insert_self u p
    simp [hup, huv] at this
  · have hpne : p.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hpne
    have hxu : x ≠ u := by intro h; subst x; exact hup hx
    have hxr : x ∈ r := by
      have : x ∈ insert u r := h.1 ▸ mem_insert_of_mem hx
      simpa [hxu] using this
    exact disjoint_left.mp hpr hx hxr

/-- For a triple family, the common-link obstruction is equivalent to literal
unordered-disjoint-union uniqueness. -/
theorem duf_iff_common_intersecting (H : Finset (Finset V))
    (hu : ∀ e ∈ H, e.card = 3) :
    DUF H ↔ ∀ q : Finset V, q.card = 2 → Intersecting (common H q) := by
  refine ⟨fun hd q hq => common_intersecting H hd q hq, ?_⟩
  intro hi A hA B hB C hC D hD hAB hCD he
  have hA3 := hu A hA
  have hC3 := hu C hC
  have hD3 := hu D hD
  have collide (C D : Finset V) (hC : C ∈ H) (hD : D ∈ H)
      (hCD : Disjoint C D) (he : A ∪ B = C ∪ D) (hAC : (A ∩ C).card = 2) : False := by
    have hC3 := hu C hC
    have hau : (A \ C).card = 1 := by rw [card_sdiff, inter_comm C A, hA3, hAC]
    have hcv : (C \ A).card = 1 := by rw [card_sdiff, hC3, hAC]
    obtain ⟨u, hU⟩ := card_eq_one.mp hau
    obtain ⟨v, hV⟩ := card_eq_one.mp hcv
    have huAC : u ∈ A ∧ u ∉ C := mem_sdiff.mp (hU.symm ▸ mem_singleton_self u)
    have hvCA : v ∈ C ∧ v ∉ A := mem_sdiff.mp (hV.symm ▸ mem_singleton_self v)
    have huv : u ≠ v := by intro h; subst u; exact hvCA.2 huAC.1
    have hAp : A = insert u (A ∩ C) := by
      have hh := sdiff_union_inter A C
      rw [hU, singleton_union] at hh
      exact hh.symm
    have hCp : C = insert v (A ∩ C) := by
      have hh := sdiff_union_inter C A
      rw [hV, inter_comm C A, singleton_union] at hh
      exact hh.symm
    have hvB : v ∈ B := by
      have hvU : v ∈ A ∪ B := he.symm ▸ mem_union_left D hvCA.1
      exact (mem_union.mp hvU).resolve_left hvCA.2
    have huD : u ∈ D := by
      have huU : u ∈ C ∪ D := he ▸ mem_union_left B huAC.1
      exact (mem_union.mp huU).resolve_left huAC.2
    let r := B.erase v
    have hr2 : r.card = 2 := by dsimp [r]; rw [card_erase_of_mem hvB, hu B hB]
    have hBr : insert v r = B := insert_erase hvB
    have hDr : insert u r = D := by
      ext x
      constructor
      · intro hx
        rcases mem_insert.mp hx with rfl | hx
        · exact huD
        · obtain ⟨hxv, hxB⟩ := mem_erase.mp hx
          have hxU : x ∈ C ∪ D := he ▸ mem_union_right A hxB
          apply (mem_union.mp hxU).resolve_left
          intro hxC
          have hxp : x ∈ A ∩ C := by
            rw [hCp] at hxC
            exact (mem_insert.mp hxC).resolve_left hxv
          exact disjoint_left.mp hAB (mem_inter.mp hxp).1 hxB
      · intro hxD
        by_cases hxu : x = u
        · exact mem_insert.mpr (Or.inl hxu)
        · have hxU : x ∈ A ∪ B := he.symm ▸ mem_union_right C hxD
          have hxB : x ∈ B := by
            apply (mem_union.mp hxU).resolve_left
            intro hxA
            rw [hAp] at hxA
            have hxp := (mem_insert.mp hxA).resolve_left hxu
            exact disjoint_left.mp hCD (mem_inter.mp hxp).2 hxD
          have hxv : x ≠ v := by intro h; subst x; exact disjoint_left.mp hCD hvCA.1 hxD
          exact mem_insert_of_mem (mem_erase.mpr ⟨hxv, hxB⟩)
    have hup : u ∉ A ∩ C := fun h => huAC.2 (mem_inter.mp h).2
    have hvp : v ∉ A ∩ C := fun h => hvCA.2 (mem_inter.mp h).1
    have hur : u ∉ r := fun h => disjoint_left.mp hAB huAC.1 (mem_erase.mp h).2
    have hvr : v ∉ r := by simp [r]
    have hpK : A ∩ C ∈ common H {u, v} := by
      refine mem_filter.mpr ⟨by simp [pairs, hAC], ?_⟩
      simp only [insert_subset_iff, singleton_subset_iff, neighbors,
        mem_filter, mem_univ, true_and]
      exact ⟨⟨hup, hAp ▸ hA⟩, ⟨hvp, hCp ▸ hC⟩⟩
    have hrK : r ∈ common H {u, v} := by
      refine mem_filter.mpr ⟨by simp [pairs, hr2], ?_⟩
      simp only [insert_subset_iff, singleton_subset_iff, neighbors,
        mem_filter, mem_univ, true_and]
      exact ⟨⟨hur, hDr.symm ▸ hD⟩, ⟨hvr, hBr.symm ▸ hB⟩⟩
    apply hi {u, v} (by simp [huv]) (A ∩ C) hpK r hrK
    exact disjoint_left.mpr fun x hx hr => disjoint_left.mp hAB (mem_inter.mp hx).1 (mem_erase.mp hr).2
  have hsplit : (A ∩ C).card + (A ∩ D).card = 3 := by
    have hACD : Disjoint (A ∩ C) (A ∩ D) := by
      exact disjoint_left.mpr fun x hx hy => disjoint_left.mp hCD (mem_inter.mp hx).2 (mem_inter.mp hy).2
    have hAU : A ∩ C ∪ A ∩ D = A := by
      ext x
      have hsub : x ∈ A → x ∈ C ∪ D := fun hx => he ▸ mem_union_left B hx
      simp only [mem_union, mem_inter] at hsub ⊢
      tauto
    rw [← card_union_of_disjoint hACD, hAU, hA3]
  by_cases hac : (A ∩ C).card = 3
  · have heAC : A = C := by
      have heA : A ∩ C = A := eq_of_subset_of_card_le inter_subset_left (by omega)
      apply eq_of_subset_of_card_le (heA ▸ inter_subset_right) (by omega)
    left
    refine ⟨heAC, ?_⟩
    subst C
    exact disjoint_injOn_union_left A hAB hCD (by simpa only [union_comm B A, union_comm D A] using he)
  by_cases had : (A ∩ D).card = 3
  · have heAD : A = D := by
      have heA : A ∩ D = A := eq_of_subset_of_card_le inter_subset_left (by omega)
      apply eq_of_subset_of_card_le (heA ▸ inter_subset_right) (by omega)
    right
    refine ⟨heAD, ?_⟩
    subst D
    exact disjoint_injOn_union_left A hAB hCD.symm (by simpa only [union_comm B A] using he)
  have htwo : (A ∩ C).card = 2 ∨ (A ∩ D).card = 2 := by omega
  rcases htwo with htwo | htwo
  · exact (collide C D hC hD hCD he htwo).elim
  · exact (collide D C hD hC hCD.symm (he.trans (union_comm C D)) htwo).elim

/-- Common links have at most four edges. A four-edge common link determines
the exact neighborhoods of the two pairs through its center. -/
theorem common_structure (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (q : Finset V) (hq : q.card = 2) :
    (common H q).card ≤ 4 ∧
      ((common H q).card = 4 → ∃ c S, c ∉ q ∧ c ∉ S ∧ S.card = 4 ∧
        common H q = star c S ∧ ∀ u ∈ q, neighbors H {c, u} = S) := by
  by_cases he : (common H q).Nonempty
  · have hp : ∀ p ∈ common H q, p.card = 2 := by
      intro p hp
      exact (mem_powersetCard.mp (mem_filter.mp hp).1).2
    rcases intersecting_classification _ hp (common_intersecting H hd q hq) he with
      ⟨c, S, hcs, heq, hSc⟩ | ⟨T, hT, heq⟩
    · have hSne : S.Nonempty := card_pos.mp (hSc.symm ▸ card_pos.mpr he)
      have hdata : ∀ u ∈ q, u ≠ c ∧ S ⊆ neighbors H {c, u} := by
        intro u hu
        have hh (s : V) (hs : s ∈ S) : u ∉ ({c, s} : Finset V) ∧
            insert u {c, s} ∈ H := by
          have hem : ({c, s} : Finset V) ∈ common H q := by
            rw [heq]; exact mem_image.mpr ⟨s, hs, rfl⟩
          have := (mem_filter.mp hem).2 hu
          simpa only [neighbors, mem_filter, mem_univ, true_and] using this
        obtain ⟨s, hs⟩ := hSne
        have huc : u ≠ c := by
          intro h; exact (hh s hs).1 (by simp [h])
        refine ⟨huc, ?_⟩
        intro t ht
        have hh' := hh t ht
        have htc : t ≠ c := by intro h; subst t; exact hcs ht
        have htu : t ≠ u := by
          intro h; subst t; exact hh'.1 (by simp)
        simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
          mem_singleton, not_or]
        exact ⟨⟨htc, htu⟩, by simpa [insert_comm, pair_comm] using hh'.2⟩
      have hS4 : S.card ≤ 4 := by
        obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < q.card)
        have hu' := hdata u hu
        exact (card_le_card hu'.2).trans (hc {c, u} (by simp [pairs, hu'.1.symm]))
      refine ⟨by omega, ?_⟩
      intro h4
      refine ⟨c, S, ?_, hcs, by omega, heq, ?_⟩
      · intro h; exact (hdata c h).1 rfl
      · intro u hu
        exact (eq_of_subset_of_card_le (hdata u hu).2 (by
          have := hc {c, u} (by simp [pairs, (hdata u hu).1.symm])
          omega)).symm
    · have ht3 : (common H q).card = 3 := by
        rw [heq, card_powersetCard, hT]; decide
      exact ⟨by omega, by omega⟩
  · have hz : (common H q).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp he)
    exact ⟨by omega, by omega⟩

/-- A nonempty exact four-neighborhood fiber is a star with at most four edges
or a triangle. The leaves of a star extend every pair joining its center to S. -/
theorem fiber_structure (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (S : Finset V) (hS : S.card = 4) :
    (fiber H S).card ≤ 4 ∧ Intersecting (fiber H S) ∧
      ((fiber H S).Nonempty →
        (∃ c A, c ∉ A ∧ c ∉ S ∧ Disjoint A S ∧
          fiber H S = star c A ∧ A.card = (fiber H S).card ∧
          ∀ s ∈ S, A ⊆ neighbors H {c, s}) ∨
        ∃ T : Finset V, T.card = 3 ∧ fiber H S = T.powersetCard 2) := by
  have hi : Intersecting (fiber H S) := by
    obtain ⟨q, hqS, hq2⟩ := exists_subset_card_eq (by omega : 2 ≤ S.card)
    intro p hp r hr
    apply common_intersecting H hd q hq2
    · exact mem_filter.mpr ⟨(mem_filter.mp hp).1, by
        rw [(mem_filter.mp hp).2]; exact hqS⟩
    · exact mem_filter.mpr ⟨(mem_filter.mp hr).1, by
        rw [(mem_filter.mp hr).2]; exact hqS⟩
  have hp : ∀ p ∈ fiber H S, p.card = 2 := by
    intro p hp
    exact (mem_powersetCard.mp (mem_filter.mp hp).1).2
  have hs : (fiber H S).Nonempty →
      (∃ c A, c ∉ A ∧ c ∉ S ∧ Disjoint A S ∧
        fiber H S = star c A ∧ A.card = (fiber H S).card ∧
        ∀ s ∈ S, A ⊆ neighbors H {c, s}) ∨
      ∃ T : Finset V, T.card = 3 ∧ fiber H S = T.powersetCard 2 := by
    intro hne
    rcases intersecting_classification _ hp hi hne with ⟨c, A, hca, he, ha⟩ | ht
    · left
      have hh (a : V) (ha : a ∈ A) (s : V) (hs : s ∈ S) :
          s ∉ ({c, a} : Finset V) ∧ insert s {c, a} ∈ H := by
        have hem : ({c, a} : Finset V) ∈ fiber H S := by
          rw [he]; exact mem_image.mpr ⟨a, ha, rfl⟩
        have : s ∈ neighbors H {c, a} := (mem_filter.mp hem).2.symm ▸ hs
        simpa only [neighbors, mem_filter, mem_univ, true_and] using this
      have hcs : c ∉ S := by
        obtain ⟨a, ha'⟩ := card_pos.mp (ha.symm ▸ card_pos.mpr hne)
        intro hcS
        exact (hh a ha' c hcS).1 (by simp)
      have hAS : Disjoint A S := by
        apply disjoint_left.mpr
        intro a ha' haS
        exact (hh a ha' a haS).1 (by simp)
      refine ⟨c, A, hca, hcs, hAS, he, ha, ?_⟩
      intro s hs a ha'
      have hac : a ≠ c := by intro h; subst a; exact hca ha'
      have has : a ≠ s := by intro h; subst a; exact disjoint_left.mp hAS ha' hs
      simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
        mem_singleton, not_or]
      exact ⟨⟨hac, has⟩, by simpa [insert_comm, pair_comm] using (hh a ha' s hs).2⟩
    · exact Or.inr ht
  refine ⟨?_, hi, hs⟩
  by_cases hne : (fiber H S).Nonempty
  · rcases hs hne with ⟨c, A, _, hcs, _, _, ha, hsub⟩ | ⟨T, hT, he⟩
    · obtain ⟨s, hs⟩ := card_pos.mp (by omega : 0 < S.card)
      have hsc : c ≠ s := by intro h; subst c; exact hcs hs
      have := (card_le_card (hsub s hs)).trans (hc {c, s} (by simp [pairs, hsc]))
      omega
    · rw [he, card_powersetCard, hT]; decide
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp

end D5.S3.Combinatorics.Graph.DUFStructure
