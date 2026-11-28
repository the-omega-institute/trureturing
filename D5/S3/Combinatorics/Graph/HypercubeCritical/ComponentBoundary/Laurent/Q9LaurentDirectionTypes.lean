/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: A connected cubic Laurent component has at most three, exactly five, or at least seven opposite-parity direction triples. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition
import Mathlib.Logic.Relation

/-! A two-step walk can change the neighbor partition only by retaining the
direction triple at its middle vertex. Once two distinct partitions share a block,
a third partition contributes at least two previously unseen triples. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions

abbrev Block := Finset (Fin 9)
abbrev Partition := Finset Block

/-- Three disjoint triples on nine axes. Their sizes force them to cover the axes. -/
structure IsTriplePartition (P : Partition) : Prop where
  card_eq : P.card = 3
  block_card : ∀ A ∈ P, A.card = 3
  disjoint_blocks : ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ≠ B → Disjoint A B

variable {P Q R : Partition} {A B S : Block}

private theorem eq_complement_of_disjoint {D : Block}
    (hA : A.card = 3) (hB : B.card = 3) (hD : D.card = 3)
    (hAB : Disjoint A B) (hDA : Disjoint D A) (hDB : Disjoint D B) :
    D = Finset.univ \ (A ∪ B) := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hiAB
    rcases Finset.mem_union.mp hiAB with hiA | hiB
    · exact (Finset.disjoint_left.mp hDA hi) hiA
    · exact (Finset.disjoint_left.mp hDB hi) hiB
  · rw [Finset.card_univ_sdiff, Fintype.card_fin, Finset.card_union_of_disjoint hAB,
      hA, hB, hD]

/-- A three-block partition contains a block distinct from any two given blocks. -/
theorem exists_third_block (hP : IsTriplePartition P) (hAB : A ≠ B) :
    ∃ D ∈ P, D ≠ A ∧ D ≠ B := by
  have hcard : ({A, B} : Partition).card < P.card := by
    rw [Finset.card_pair hAB, hP.card_eq]
    omega
  obtain ⟨D, hDP, hD⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨D, hDP, fun h => hD (Finset.mem_insert.mpr (Or.inl h)),
    fun h => hD (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))⟩

private theorem mem_of_disjoint_from_two (hP : IsTriplePartition P)
    (hAP : A ∈ P) (hBP : B ∈ P) (hAB : A ≠ B) {D : Block}
    (hD : D.card = 3) (hDA : Disjoint D A) (hDB : Disjoint D B) : D ∈ P := by
  obtain ⟨E, hEP, hEA, hEB⟩ := exists_third_block hP hAB
  have hAd := hP.disjoint_blocks hAP hBP hAB
  have hDcomp := eq_complement_of_disjoint (hP.block_card A hAP) (hP.block_card B hBP)
    hD hAd hDA hDB
  have hEcomp := eq_complement_of_disjoint (hP.block_card A hAP) (hP.block_card B hBP)
    (hP.block_card E hEP) hAd (hP.disjoint_blocks hEP hAP hEA)
    (hP.disjoint_blocks hEP hBP hEB)
  rw [hDcomp.trans hEcomp.symm]
  exact hEP

/-- Two distinct shared blocks determine the entire partition. -/
theorem eq_of_two_common_blocks (hP : IsTriplePartition P) (hQ : IsTriplePartition Q)
    (hAP : A ∈ P) (hBP : B ∈ P) (hAQ : A ∈ Q) (hBQ : B ∈ Q) (hAB : A ≠ B) :
    P = Q := by
  apply Finset.eq_of_subset_of_card_le
  · intro D hDP
    by_cases hDA : D = A
    · simpa only [hDA] using hAQ
    by_cases hDB : D = B
    · simpa only [hDB] using hBQ
    exact mem_of_disjoint_from_two hQ hAQ hBQ hAB (hP.block_card D hDP)
      (hP.disjoint_blocks hDP hAP hDA) (hP.disjoint_blocks hDP hBP hDB)
  · rw [hP.card_eq, hQ.card_eq]

/-- Distinct partitions sharing `S` have intersection exactly `{S}`. -/
theorem inter_eq_singleton (hP : IsTriplePartition P) (hQ : IsTriplePartition Q)
    (hPQ : P ≠ Q) (hSP : S ∈ P) (hSQ : S ∈ Q) : P ∩ Q = {S} := by
  ext D
  constructor
  · intro hD
    obtain ⟨hDP, hDQ⟩ := Finset.mem_inter.mp hD
    apply Finset.mem_singleton.mpr
    by_contra hDS
    exact hPQ (eq_of_two_common_blocks hP hQ hDP hSP hDQ hSQ hDS)
  · intro hD
    have hDS := Finset.mem_singleton.mp hD
    subst D
    exact Finset.mem_inter.mpr ⟨hSP, hSQ⟩

theorem card_union_eq_five (hP : IsTriplePartition P) (hQ : IsTriplePartition Q)
    (hPQ : P ≠ Q) (hSP : S ∈ P) (hSQ : S ∈ Q) : (P ∪ Q).card = 5 := by
  have hsum := Finset.card_union_add_card_inter P Q
  rw [inter_eq_singleton hP hQ hPQ hSP hSQ, Finset.card_singleton,
    hP.card_eq, hQ.card_eq] at hsum
  omega

private theorem eq_left_or_right_of_cross_pair (hP : IsTriplePartition P)
    (hQ : IsTriplePartition Q) (hR : IsTriplePartition R) (hSP : S ∈ P) (hSQ : S ∈ Q)
    (hAP : A ∈ P) (hBQ : B ∈ Q) (hAR : A ∈ R) (hBR : B ∈ R) (hAB : A ≠ B) :
    R = P ∨ R = Q := by
  by_cases hAQ : A ∈ Q
  · exact Or.inr (eq_of_two_common_blocks hR hQ hAR hBR hAQ hBQ hAB)
  have hAS : A ≠ S := by
    intro hAS
    exact hAQ (by simpa only [hAS] using hSQ)
  have hBP : B ∈ P := by
    by_cases hBS : B = S
    · simpa only [hBS] using hSP
    -- Outside `S`, the block complementary to `A` is forced by disjointness.
    exact mem_of_disjoint_from_two hP hAP hSP hAS (hQ.block_card B hBQ)
      (hR.disjoint_blocks hBR hAR hAB.symm) (hQ.disjoint_blocks hBQ hSQ hBS)
  exact Or.inl (eq_of_two_common_blocks hR hP hAR hBR hAP hBP hAB)

/-- A partition with two distinct blocks in the union of two overlapping partitions
is one of those partitions. -/
theorem eq_left_or_right_of_two_blocks_in_union (hP : IsTriplePartition P)
    (hQ : IsTriplePartition Q) (hR : IsTriplePartition R) (hSP : S ∈ P) (hSQ : S ∈ Q)
    (hAR : A ∈ R) (hBR : B ∈ R) (hAB : A ≠ B) (hA : A ∈ P ∪ Q) (hB : B ∈ P ∪ Q) :
    R = P ∨ R = Q := by
  rcases Finset.mem_union.mp hA with hAP | hAQ <;>
    rcases Finset.mem_union.mp hB with hBP | hBQ
  · exact Or.inl (eq_of_two_common_blocks hR hP hAR hBR hAP hBP hAB)
  · exact eq_left_or_right_of_cross_pair hP hQ hR hSP hSQ hAP hBQ hAR hBR hAB
  · exact (eq_left_or_right_of_cross_pair hQ hP hR hSQ hSP hAQ hBP hAR hBR hAB).symm
  · exact Or.inr (eq_of_two_common_blocks hR hQ hAR hBR hAQ hBQ hAB)

/-- A third partition contributes at least two blocks outside the union of an overlapping pair. -/
theorem two_le_card_sdiff_union_of_third (hP : IsTriplePartition P) (hQ : IsTriplePartition Q)
    (hR : IsTriplePartition R) (hSP : S ∈ P) (hSQ : S ∈ Q) (hRP : R ≠ P) (hRQ : R ≠ Q) :
    2 ≤ (R \ (P ∪ Q)).card := by
  have hle : ((P ∪ Q) ∩ R).card ≤ 1 := by
    by_contra hle
    have hlt : 1 < ((P ∪ Q) ∩ R).card := Nat.lt_of_not_ge hle
    obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp hlt
    obtain ⟨hAU, hAR⟩ := Finset.mem_inter.mp hA
    obtain ⟨hBU, hBR⟩ := Finset.mem_inter.mp hB
    exact (eq_left_or_right_of_two_blocks_in_union hP hQ hR hSP hSQ hAR hBR hAB hAU hBU).elim
      hRP hRQ
  rw [Finset.card_sdiff, hR.card_eq]
  omega

/-- The set of all block types occurring in a finite family. -/
def blockTypes (family : Finset Partition) : Finset Block := family.biUnion id

private theorem subset_blockTypes {family : Finset Partition} (hP : P ∈ family) :
    P ⊆ blockTypes family := by
  intro D hD
  change D ∈ family.biUnion id
  exact Finset.mem_biUnion.mpr ⟨P, hP, hD⟩

/-- A family containing distinct partitions `P` and `Q` with common block `S`
has at least seven types or consists of precisely that pair with five types. -/
theorem seven_le_card_types_or_eq_pair (family : Finset Partition)
    (hfamily : ∀ T ∈ family, IsTriplePartition T)
    (hP : P ∈ family) (hQ : Q ∈ family) (hPQ : P ≠ Q) (hSP : S ∈ P) (hSQ : S ∈ Q) :
    7 ≤ (blockTypes family).card ∨
      (family = {P, Q} ∧ P ∩ Q = {S} ∧ (blockTypes family).card = 5) := by
  have hPU := subset_blockTypes hP
  have hQU := subset_blockTypes hQ
  have hU : P ∪ Q ⊆ blockTypes family := Finset.union_subset hPU hQU
  have hcard := card_union_eq_five (hfamily P hP) (hfamily Q hQ) hPQ hSP hSQ
  by_cases hseven : 7 ≤ (blockTypes family).card
  · exact Or.inl hseven
  have hpair : family = {P, Q} := by
    ext R
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hR
      by_cases hRP : R = P
      · exact Or.inl hRP
      by_cases hRQ : R = Q
      · exact Or.inr hRQ
      exfalso
      have hnew := two_le_card_sdiff_union_of_third (hfamily P hP) (hfamily Q hQ)
        (hfamily R hR) hSP hSQ hRP hRQ
      have hsum := Finset.card_sdiff_add_card R (P ∪ Q)
      rw [hcard] at hsum
      have hle := Finset.card_le_card (Finset.union_subset (subset_blockTypes hR) hU)
      omega
    · rintro (rfl | rfl)
      · exact hP
      · exact hQ
  have htypes : blockTypes family = P ∪ Q := by
    refine Finset.Subset.antisymm ?_ hU
    intro D hD
    change D ∈ family.biUnion id at hD
    obtain ⟨T, hT, hDT⟩ := Finset.mem_biUnion.mp hD
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl hDT)
    · exact Finset.mem_union.mpr (Or.inr hDT)
  exact Or.inr ⟨hpair, inter_eq_singleton (hfamily P hP) (hfamily Q hQ) hPQ hSP hSQ,
    by simpa only [htypes] using hcard⟩

/-- A family with five types consists of two distinct partitions with one common block. -/
theorem exists_pair_of_card_types_eq_five (family : Finset Partition)
    (hfamily : ∀ T ∈ family, IsTriplePartition T) (hfive : (blockTypes family).card = 5) :
    ∃ P Q : Partition, ∃ S : Block,
      P ≠ Q ∧ family = {P, Q} ∧ P ∩ Q = {S} := by
  obtain ⟨A, hA⟩ := Finset.card_pos.mp (show 0 < (blockTypes family).card by omega)
  change A ∈ family.biUnion id at hA
  obtain ⟨P, hP, _⟩ := Finset.mem_biUnion.mp hA
  have hex : ∃ Q ∈ family, P ≠ Q := by
    by_contra hnone
    have hsub : blockTypes family ⊆ P := by
      intro D hD
      change D ∈ family.biUnion id at hD
      obtain ⟨Q, hQ, hDQ⟩ := Finset.mem_biUnion.mp hD
      by_cases hPQ : P = Q
      · subst Q
        exact hDQ
      · exact (hnone ⟨Q, hQ, hPQ⟩).elim
    have hle := Finset.card_le_card hsub
    rw [hfive, (hfamily P hP).card_eq] at hle
    omega
  obtain ⟨Q, hQ, hPQ⟩ := hex
  have hsub := Finset.union_subset (subset_blockTypes hP) (subset_blockTypes hQ)
  have hle := Finset.card_le_card hsub
  have hsum := Finset.card_union_add_card_inter P Q
  rw [(hfamily P hP).card_eq, (hfamily Q hQ).card_eq] at hsum
  obtain ⟨S, hS⟩ := Finset.card_pos.mp (show 0 < (P ∩ Q).card by omega)
  obtain ⟨hSP, hSQ⟩ := Finset.mem_inter.mp hS
  rcases seven_le_card_types_or_eq_pair family hfamily hP hQ hPQ hSP hSQ with hseven | hpair
  · omega
  · exact ⟨P, Q, S, hPQ, hpair.1, hpair.2.1⟩

section Laurent

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (flip)
open BalancedCubeComponentBoundary (directions)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity neighbor_triples_partition)

/-- The direction blocks at the internal neighbors of a Laurent row vertex. -/
noncomputable def neighborPartition (C : Finset (BalancedCriticalSpectrum.Q 9))
    (x : BalancedCriticalSpectrum.Q 9) : Partition :=
  (directions C x).image fun i => directions C (flip x i)

open scoped Classical in
theorem isTriplePartition_neighborPartition {C : Finset (BalancedCriticalSpectrum.Q 9)}
    {b : Bool} {a : Side C b → Exponent}
    (hC : ((hypercube 9).induce (C : Set (BalancedCriticalSpectrum.Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) (x : Side C b) : IsTriplePartition (neighborPartition C x.val) := by
  obtain ⟨hdegree, hcard, huniq⟩ := neighbor_triples_partition hC h x
  let block (i : Fin 9) : Block := directions C (flip x.val i)
  change IsTriplePartition ((directions C x.val).image block)
  have same_index {i j k : Fin 9} (hi : i ∈ directions C x.val) (hj : j ∈ directions C x.val)
      (hki : k ∈ block i) (hkj : k ∈ block j) : i = j := by
    obtain ⟨u, _, hu⟩ := huniq k
    exact congrArg Subtype.val ((hu ⟨i, hi⟩ hki).trans (hu ⟨j, hj⟩ hkj).symm)
  have hinj : Set.InjOn block (↑(directions C x.val) : Set (Fin 9)) := by
    intro i hi j hj hij
    have hc : (block i).card = 3 := hcard i hi
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < (block i).card by omega)
    have hkj : k ∈ block j := by rwa [← hij]
    exact same_index hi hj hk hkj
  refine ⟨(Finset.card_image_iff.mpr hinj).trans hdegree, ?_, ?_⟩
  · intro A hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
    exact hcard i hi
  · intro A hA B hB hAB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    exact hAB (congrArg block (same_index hi hj hki hkj))

end Laurent

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity)
open private flip_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition

/-- The distinct neighbor partitions on the selected parity. -/
noncomputable def partitionsOn (C : Finset (Q 9)) (b : Bool) : Finset Partition := by
  classical
  exact univ.image fun x : Side C b => neighborPartition C x.val

/-- The distinct direction blocks on the opposite parity. -/
noncomputable def directionTypes (C : Finset (Q 9)) (b : Bool) : Finset Block := by
  classical
  exact univ.image fun x : Side C (!b) => directions C x.val

open scoped Classical in
/-- Every opposite-parity cubic vertex contributes its direction triple to
at least one selected-parity neighbor partition. -/
theorem blockTypes_partitionsOn {C : Finset (Q 9)} {b : Bool}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    blockTypes (partitionsOn C b) = directionTypes C b := by
  classical
  ext S
  change S ∈ (partitionsOn C b).biUnion id ↔ S ∈ directionTypes C b
  rw [mem_biUnion]
  constructor
  · rintro ⟨P, hP, hS⟩
    obtain ⟨x, _, rfl⟩ := mem_image.mp hP
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hS
    have hv : cubeFlip x.val i ∈ C := (mem_directions C _ _).mp hi
    have hp : Q9IsotropicHuang.parity (cubeFlip x.val i) = !b := by
      rw [flip_parity, x.property.2]
    exact mem_image.mpr ⟨⟨cubeFlip x.val i, hv, hp⟩, mem_univ _, rfl⟩
  · intro hS
    obtain ⟨v, _, rfl⟩ := mem_image.mp hS
    have hv := regular_directions C hC v.property.1
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < (directions C v.val).card)
    let x : Side C b := ⟨cubeFlip v.val i, (mem_directions C _ _).mp hi, by
      rw [flip_parity, v.property.2, Bool.not_not]⟩
    refine ⟨neighborPartition C x.val, mem_image.mpr ⟨x, mem_univ _, rfl⟩, ?_⟩
    have hx : cubeFlip x.val i = v.val := BalancedCriticalSpectrum.flip_flip _ _
    exact mem_image.mpr ⟨i, (mem_directions C _ _).mpr (hx.symm ▸ v.property.1), by rw [hx]⟩

open scoped Classical in
/-- If exactly five triples occur then each row uses one of two partitions.
Their unique shared triple occurs at every selected vertex. -/
theorem two_partitions_of_five_directionTypes {C : Finset (Q 9)} {b : Bool}
    {a : Side C b → Exponent}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (h : LaurentIdentity a)
    (hfive : (directionTypes C b).card = 5) :
    ∃ (P R : Partition) (S : Block),
      P ≠ R ∧ IsTriplePartition P ∧ IsTriplePartition R ∧
        P ∩ R = {S} ∧ partitionsOn C b = {P, R} := by
  have hPart : ∀ P ∈ partitionsOn C b, IsTriplePartition P := by
    intro P hP
    obtain ⟨x, _, rfl⟩ := mem_image.mp hP
    exact isTriplePartition_neighborPartition hC h x
  obtain ⟨P, R, S, hne, hfamily, hinter⟩ := exists_pair_of_card_types_eq_five
    (partitionsOn C b) hPart (by rwa [blockTypes_partitionsOn hC])
  have hp : P ∈ partitionsOn C b := by simp [hfamily]
  have hr : R ∈ partitionsOn C b := by simp [hfamily]
  exact ⟨P, R, S, hne, hPart P hp, hPart R hr, hinter, hfamily⟩


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9ProjectedWalk

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open Q9IsotropicHuang (parity)
open Q9LaurentGainPartition (Side)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

variable {C : Finset (Q 9)} {b : Bool}
private abbrev supportGraph (C : Finset (Q 9)) := (hypercube 9).induce (C : Set (Q 9))

private theorem other_parity {u v : ↥C} (h : (supportGraph C).Adj u v) :
    parity v.val = !parity u.val :=
  Bool.eq_not_of_ne (Ne.symm (cubeParity_ne_of_adj h))

private theorem not_other (p : Bool) : p ≠ !p := by cases p <;> decide

/-- A walk between selected-parity vertices projects to a path in any
relation that contains the images of their actual two-step moves. -/
theorem projected_of_walk {α : Type*} {R : α → α → Prop} (f : Side C b → α)
    (hstep : ∀ (x y : Side C b) (v : ↥C),
      (supportGraph C).Adj ⟨x.val, x.property.1⟩ v → (supportGraph C).Adj v ⟨y.val, y.property.1⟩ →
      Relation.ReflTransGen R (f x) (f y))
    {u v : ↥C} (w : (supportGraph C).Walk u v) (hu : parity u.val = b) (hv : parity v.val = b) :
    Relation.ReflTransGen R (f ⟨u.val, u.property, hu⟩) (f ⟨v.val, v.property, hv⟩) := by
  have walkImage {a z : ↥C} (path : (supportGraph C).Walk a z) (hz : parity z.val = b) :
      (∀ ha : parity a.val = b, Relation.ReflTransGen R
        (f ⟨a.val, a.property, ha⟩) (f ⟨z.val, z.property, hz⟩)) ∧
      (∀ (x : Side C b), (supportGraph C).Adj ⟨x.val, x.property.1⟩ a →
        parity a.val = !b → Relation.ReflTransGen R (f x) (f ⟨z.val, z.property, hz⟩)) := by
    induction path with
    | nil =>
      refine ⟨fun _ => .refl, ?_⟩
      intro _ _ ha
      exact (not_other b (hz.symm.trans ha)).elim
    | cons edge tail ih =>
      constructor
      · intro ha
        exact (ih hz).2 ⟨_, Subtype.property _, ha⟩ edge
          ((other_parity edge).trans (congrArg Bool.not ha))
      · intro x hx ha
        have hz' := (other_parity edge).trans (congrArg Bool.not ha)
        rw [Bool.not_not] at hz'
        exact (hstep x ⟨_, Subtype.property _, hz'⟩ _ hx edge).trans ((ih hz).1 hz')
  exact (walkImage w hv).1 hu

/-- The projection of a connected induced cube support is connected under
images of the selected-parity two-step moves. -/
theorem projected_of_connected {α : Type*} {R : α → α → Prop} (f : Side C b → α)
    (hc : (supportGraph C).Connected)
    (hstep : ∀ (x y : Side C b) (v : ↥C),
      (supportGraph C).Adj ⟨x.val, x.property.1⟩ v → (supportGraph C).Adj v ⟨y.val, y.property.1⟩ →
      Relation.ReflTransGen R (f x) (f y)) (x y : Side C b) :
    Relation.ReflTransGen R (f x) (f y) := by
  obtain ⟨w⟩ := hc.preconnected (⟨x.val, x.property.1⟩ : ↥C) ⟨y.val, y.property.1⟩
  exact projected_of_walk f hstep w x.property.2 y.property.2


end Q9ProjectedWalk
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q flip)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity)
open BalancedCubeGirth (adjacent_exists_flip)

private theorem directions_mem_neighborPartition {C : Finset (Q 9)} {x v : ↥C}
    (h : ((hypercube 9).induce (C : Set (Q 9))).Adj x v) :
    directions C v.val ∈ neighborPartition C x.val := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip h
  change v.val = flip x.val i at hi
  exact mem_image.mpr ⟨i, (mem_directions C _ _).mpr (hi ▸ v.property), by rw [← hi]⟩

/-- Every nonconstant family of neighbor partitions in a connected support
contains two distinct partitions sharing the directions of an intermediate vertex. -/
private theorem exists_overlapping_partitions {C : Finset (Q 9)} {b : Bool}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (x y : Side C b) (hne : neighborPartition C x.val ≠ neighborPartition C y.val) :
    ∃ P ∈ partitionsOn C b, ∃ R ∈ partitionsOn C b, P ≠ R ∧ ∃ S, S ∈ P ∧ S ∈ R := by
  by_contra hnone
  have hstep (a z : Side C b) (v : ↥C)
      (ha : ((hypercube 9).induce (C : Set (Q 9))).Adj ⟨a.val, a.property.1⟩ v)
      (hz : ((hypercube 9).induce (C : Set (Q 9))).Adj v ⟨z.val, z.property.1⟩) :
      Relation.ReflTransGen Eq (neighborPartition C a.val) (neighborPartition C z.val) := by
    apply Relation.ReflTransGen.single
    by_contra hne'
    have haPart : neighborPartition C a.val ∈ partitionsOn C b :=
      mem_image.mpr ⟨a, mem_univ _, rfl⟩
    have hzPart : neighborPartition C z.val ∈ partitionsOn C b :=
      mem_image.mpr ⟨z, mem_univ _, rfl⟩
    have haBlock : directions C v.val ∈ neighborPartition C a.val :=
      directions_mem_neighborPartition (C := C) (x := ⟨a.val, a.property.1⟩) (v := v) ha
    have hzBlock : directions C v.val ∈ neighborPartition C z.val :=
      directions_mem_neighborPartition (C := C) (x := ⟨z.val, z.property.1⟩) (v := v) hz.symm
    exact hnone ⟨_, haPart, _, hzPart, hne', _, haBlock, hzBlock⟩
  have walk := Q9ProjectedWalk.projected_of_connected
    (fun a : Side C b => neighborPartition C a.val) hc hstep x y
  rw [Relation.reflTransGen_eq_self] at walk
  exact hne walk

open scoped Classical in
/-- For a connected cubic Laurent component, a nonconstant neighbor partition
forces either five distinct opposite-parity direction triples or at least seven.
A constant partition contributes at most three. -/
theorem card_directionTypes_le_three_or_eq_five_or_ge_seven
    {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) :
    (directionTypes C b).card ≤ 3 ∨ (directionTypes C b).card = 5 ∨
      7 ≤ (directionTypes C b).card := by
  classical
  by_cases hsmall : (directionTypes C b).card ≤ 3
  · exact Or.inl hsmall
  right
  rw [← blockTypes_partitionsOn hC] at hsmall ⊢
  have hPart : ∀ P ∈ partitionsOn C b, IsTriplePartition P := by
    intro P hP
    obtain ⟨x, _, rfl⟩ := mem_image.mp hP
    exact isTriplePartition_neighborPartition hC h x
  obtain ⟨S, hS⟩ := card_pos.mp (show 0 < (blockTypes (partitionsOn C b)).card by omega)
  obtain ⟨P, hP, _⟩ := mem_biUnion.mp hS
  obtain ⟨R, hR, hPR⟩ : ∃ R ∈ partitionsOn C b, P ≠ R := by
    by_contra hnone
    have hsub : blockTypes (partitionsOn C b) ⊆ P := by
      intro T hT
      obtain ⟨U, hU, hTU⟩ := mem_biUnion.mp hT
      have hPU : P = U := Classical.byContradiction fun hne => hnone ⟨U, hU, hne⟩
      exact hPU.symm ▸ hTU
    apply hsmall
    simpa only [(hPart P hP).card_eq] using card_le_card hsub
  obtain ⟨x, _, rfl⟩ := mem_image.mp hP
  obtain ⟨y, _, rfl⟩ := mem_image.mp hR
  obtain ⟨P, hP, R, hR, hPR, T, hTP, hTR⟩ := exists_overlapping_partitions hc x y hPR
  rcases seven_le_card_types_or_eq_pair _ hPart hP hR hPR hTP hTR with hseven | hpair
  · exact Or.inr hseven
  · exact Or.inl hpair.2.2

end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
