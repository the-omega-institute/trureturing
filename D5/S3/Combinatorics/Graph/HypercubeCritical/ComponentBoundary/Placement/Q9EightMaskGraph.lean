/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A minimum-degree-three graph with eight edges is complete on five vertices with two disjoint edges removed. -/

module

public import Mathlib.Data.Finset.Powerset
import all D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
import Batteries.Tactic.OpenPrivate

/-! The missing edges of an eight-edge mask graph are a matching on five axes. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskGraph

open Finset
open private axes extensions mem_axes mem_extensions weight_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

private theorem extensions_bound {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)}
    (hthree : ∀ T ∈ F, ∀ i ∈ T,
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (∀ j ∈ ({a, b, c} : Finset α), j ∉ T.erase i ∧ insert j (T.erase i) ∈ F)) :
    ∀ T ∈ F, ∀ i ∈ T, 3 ≤ (extensions F (T.erase i)).card := by
  intro T hT i hi
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := hthree T hT i hi
  have hsub : ({a, b, c} : Finset α) ⊆ extensions F (T.erase i) :=
    fun j hj => mem_extensions.mpr (he j hj)
  simpa [hab, hac, hbc] using card_le_card hsub

/-- The handshake bound allows no seven-edge graph of minimum degree three on its support. -/
public theorem eight_le_of_three_extensions_of_card_ne_six {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hne : F.Nonempty)
    (hsize : ∀ T ∈ F, T.card = 2)
    (hthree : ∀ T ∈ F, ∀ i ∈ T,
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (∀ j ∈ ({a, b, c} : Finset α), j ∉ T.erase i ∧ insert j (T.erase i) ∈ F))
    (h6 : F.card ≠ 6) : 8 ≤ F.card := by
  obtain ⟨hlower, hweight⟩ := weight_count 2 F hne hsize (extensions_bound hthree)
  obtain ⟨_, hincidence⟩ := hweight (by decide)
  change 6 ≤ F.card at hlower
  change (axes F).card * 3 ≤ 2 * F.card at hincidence
  by_contra! hlt
  have hsmall : (axes F).card ≤ 4 := by omega
  have hsub : F ⊆ (axes F).powersetCard 2 :=
    fun T hT => mem_powersetCard.mpr ⟨fun i hi => mem_axes.mpr ⟨T, hT, hi⟩, hsize T hT⟩
  have hbound := card_le_card hsub
  rw [card_powersetCard] at hbound
  have hchoose : ((axes F).card).choose 2 ≤ 6 := Nat.choose_le_choose 2 hsmall
  omega

/-- Every eight-edge simple graph of minimum degree three on its support is
the complete graph on five vertices with a matching of two edges deleted. -/
public theorem eight_edge_family_eq_delete_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hF : F.card = 8)
    (hsize : ∀ T ∈ F, T.card = 2)
    (hthree : ∀ T ∈ F, ∀ i ∈ T,
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (∀ j ∈ ({a, b, c} : Finset α), j ∉ T.erase i ∧ insert j (T.erase i) ∈ F)) :
    ∃ A P R : Finset α, A.card = 5 ∧ P ∈ A.powersetCard 2 ∧ R ∈ A.powersetCard 2 ∧
      Disjoint P R ∧ F = A.powersetCard 2 \ {P, R} := by
  have hext := extensions_bound hthree
  let A := axes F
  have hne : F.Nonempty := card_pos.mp (by omega)
  obtain ⟨_, hw⟩ := weight_count 2 F hne hsize hext
  obtain ⟨_, hi⟩ := hw (by decide)
  change A.card * 3 ≤ 2 * F.card at hi
  have hsub : F ⊆ A.powersetCard 2 := fun T hT =>
    mem_powersetCard.mpr ⟨fun j hj => mem_axes.mpr ⟨T, hT, hj⟩, hsize T hT⟩
  have hA : A.card = 5 := by
    have hcap := card_le_card hsub
    rw [card_powersetCard, hF] at hcap
    by_contra! hne
    have hsmall : A.card ≤ 4 := by omega
    have hchoose : A.card.choose 2 ≤ 6 := Nat.choose_le_choose 2 hsmall
    omega
  let M := A.powersetCard 2 \ F
  have hM : M.card = 2 := by
    dsimp only [M]
    rw [card_sdiff_of_subset hsub, card_powersetCard, hA, hF]
    decide
  obtain ⟨P, R, hPR, he⟩ := card_eq_two.mp hM
  have hPM : P ∈ M := he.symm ▸ mem_insert_self _ _
  have hRM : R ∈ M := he.symm ▸ mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨hP, hPF⟩ := mem_sdiff.mp hPM
  obtain ⟨hR, hRF⟩ := mem_sdiff.mp hRM
  refine ⟨A, P, R, hA, hP, hR, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro v hvP hvR
    have hvA := (mem_powersetCard.mp hP).1 hvP
    obtain ⟨T, hT, hv⟩ := mem_axes.mp hvA
    obtain ⟨i, hi, hiv⟩ := exists_mem_ne (by rw [hsize T hT]; decide) v
    have herase : T.erase i = {v} := by
      symm
      apply eq_of_subset_of_card_le
      · exact singleton_subset_iff.mpr (mem_erase.mpr ⟨hiv.symm, hv⟩)
      · rw [card_singleton, card_erase_of_mem hi, hsize T hT]
    have h3 := hext T hT i hi
    rw [herase] at h3
    have hinj : Set.InjOn (fun j => insert v ({j} : Finset α)) (extensions F {v} : Set α) := by
      intro j hj k hk heq
      have hjv : j ≠ v := fun h => (mem_extensions.mp hj).1 (mem_singleton.mpr h)
      change ({v, j} : Finset α) = {v, k} at heq
      have hj' : j ∈ ({v, k} : Finset α) := by
        rw [← heq]
        exact mem_insert_of_mem (mem_singleton_self j)
      exact mem_singleton.mp ((mem_insert.mp hj').resolve_left hjv)
    let E := (extensions F {v}).image (fun j => insert v ({j} : Finset α))
    have hEA : E ⊆ (A.powersetCard 2).filter ({v} ⊆ ·) := by
      intro U hU
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hU
      have hJF := (mem_extensions.mp hj).2
      rw [show insert v ({j} : Finset α) = insert j {v} by exact Finset.pair_comm _ _]
      exact mem_filter.mpr ⟨hsub hJF, singleton_subset_iff.mpr
        (mem_insert_of_mem (mem_singleton_self _))⟩
    have hEF : E ⊆ F := by
      intro U hU
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hU
      simpa only [Finset.pair_comm j v] using (mem_extensions.mp hj).2
    have hP' : P ∈ (A.powersetCard 2).filter ({v} ⊆ ·) :=
      mem_filter.mpr ⟨hP, singleton_subset_iff.mpr hvP⟩
    have hR' : R ∈ (A.powersetCard 2).filter ({v} ⊆ ·) :=
      mem_filter.mpr ⟨hR, singleton_subset_iff.mpr hvR⟩
    have hUnion : insert P (insert R E) ⊆ (A.powersetCard 2).filter ({v} ⊆ ·) :=
      insert_subset hP' (insert_subset hR' hEA)
    have hcard := card_le_card hUnion
    rw [card_filter_powersetCard_subset {v} A 2 (singleton_subset_iff.mpr hvA) (by simp),
      card_singleton, hA] at hcard
    rw [card_insert_of_notMem (fun h => (mem_insert.mp h).elim hPR (fun hp => hPF (hEF hp))),
      card_insert_of_notMem (fun h => hRF (hEF h))] at hcard
    have hCardE : E.card = (extensions F {v}).card := card_image_of_injOn hinj
    rw [hCardE] at hcard
    change (extensions F {v}).card + 1 + 1 ≤ 4 at hcard
    omega
  · rw [← he]
    change F = A.powersetCard 2 \ (A.powersetCard 2 \ F)
    ext T
    simp only [mem_sdiff]
    constructor
    · exact fun hT => ⟨hsub hT, fun h => h.2 hT⟩
    · exact fun hT => by_contra fun hn => hT.2 ⟨hT.1, hn⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskGraph
