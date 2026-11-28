/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound]
   utility: none
   digest: Finite group divisible designs attain the cooling-code leave bound. -/

import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.FiniteBound

/-! # Cooling codes from uniform group divisible designs -/

open scoped BigOperators
open Finset SimpleGraph

namespace CPECCBridge

/-- The equivalence classes of the setoid are the groups. A distinct within-group pair occurs
in no block, and a cross-group pair occurs in exactly one block. -/
structure GroupDivisibleDesign (V : Type*) [DecidableEq V] (k g : ℕ) where
  groups : Setoid V
  group_card : ∀ v, ({u | groups.r v u} : Set V).ncard = g
  blocks : Finset (Finset V)
  block_card : ∀ B ∈ blocks, B.card = k
  within_group : ∀ B ∈ blocks, ∀ ⦃u v⦄, u ∈ B → v ∈ B → u ≠ v → ¬ groups.r u v
  cross_group : ∀ ⦃u v⦄, ¬ groups.r u v → ∃! B, B ∈ blocks ∧ u ∈ B ∧ v ∈ B

/-- A family of information classes in the support model for correction radius $w-2$. -/
def IsSupportFamily {V I : Type*} [DecidableEq V]
    (P : I → Finset (Finset V)) (w t : ℕ) : Prop :=
  (∀ i A, A ∈ P i → A.card = w) ∧
  (∀ i (D : Finset V), D.card = t → ∃ A ∈ P i, Disjoint D A) ∧
  (∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ B ∈ P j, (A ∩ B).card ≤ 1)

private theorem design_blocks_inter_le_one {V : Type*} [DecidableEq V] {k g : ℕ}
    (G : GroupDivisibleDesign V k g) :
    ∀ ⦃A B : Finset V⦄, A ∈ G.blocks → B ∈ G.blocks → A ≠ B → (A ∩ B).card ≤ 1 := by
  intro A B hA hB hne
  by_contra! hcard
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨C, _, hC⟩ := G.cross_group (G.within_group A hA huA hvA huv)
  exact hne ((hC A ⟨hA, huA, hvA⟩).trans (hC B ⟨hB, huB, hvB⟩).symm)

private theorem design_block_count {V : Type*} [Fintype V] [DecidableEq V]
    {k g : ℕ} (G : GroupDivisibleDesign V k g) (hk : 2 ≤ k) :
    G.blocks.card = Fintype.card V * (Fintype.card V - g) / (k * (k - 1)) := by
  classical
  let H := packedGraph G.blocks id
  let : DecidableRel H.Adj := Classical.decRel _
  have hdegree (v : V) : H.degree v = Fintype.card V - g := by
    rw [← H.ncard_neighborSet]
    have hneighbors : H.neighborSet v = ({u | G.groups.r v u} : Set V)ᶜ := by
      ext u
      change H.Adj v u ↔ ¬ G.groups.r v u
      rw [packedGraph_adj_iff]
      constructor
      · rintro ⟨B, hB, hv, hu⟩
        obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
        exact G.within_group B hB hv hu hne.symm
      · intro h
        obtain ⟨B, ⟨hB, hv, hu⟩, _⟩ := G.cross_group h
        have hne : u ≠ v := fun he => h (he ▸ G.groups.refl v)
        exact ⟨B, hB, hv, Finset.mem_erase.mpr ⟨hne, hu⟩⟩
    rw [hneighbors, Set.ncard_compl, G.group_card, Nat.card_eq_fintype_card]
  have hsum : (∑ v : V, H.degree v) = Fintype.card V * (Fintype.card V - g) := by
    simp [hdegree]
  have hincidence : (∑ v : V, (G.blocks.filter (fun B => v ∈ B)).card) =
      k * G.blocks.card := by
    simpa only [id_eq] using incidence_sum G.blocks id k G.block_card
  rw [show (∑ v : V, H.degree v) =
      ∑ v : V, (k - 1) * (G.blocks.filter (fun B => v ∈ B)).card by
        exact Finset.sum_congr rfl fun v _ =>
          packedGraph_degree G.blocks id k G.block_card (design_blocks_inter_le_one G) v,
    ← Finset.mul_sum, hincidence] at hsum
  symm
  apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (by omega) (by omega))
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum.symm

private def WSubsets {V : Type*} [DecidableEq V]
    (B : Finset V) (w : ℕ) : Finset (Finset V) :=
  B.powerset.filter (fun A => A.card = w)

private theorem wsubsets_mem_size {V : Type*} [DecidableEq V]
    {B A : Finset V} {w : ℕ} (hA : A ∈ WSubsets B w) : A.card = w := by
  exact (Finset.mem_filter.mp hA).2

private theorem wsubsets_mem_subset {V : Type*} [DecidableEq V]
    {B A : Finset V} {w : ℕ} (hA : A ∈ WSubsets B w) : A ⊆ B := by
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1

private theorem wsubsets_survives_deletion {V : Type*} [DecidableEq V]
    {B : Finset V} {w t : ℕ} (_hB : B.card = w + t)
    (S : Finset V) (_hS : S.card = t) (hwt : w ≤ (B \ S).card) :
    ∃ A ∈ WSubsets B w, Disjoint S A := by
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hwt
  refine ⟨A, ?_, Finset.disjoint_of_subset_right hA ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hA.trans Finset.sdiff_subset), hAcard⟩
  · exact Finset.disjoint_sdiff

private theorem wsubsets_deletion_of_block_size {V : Type*} [DecidableEq V]
    {B : Finset V} {w t : ℕ} (hB : B.card = w + t)
    (S : Finset V) (hS : S.card = t) :
    ∃ A ∈ WSubsets B w, Disjoint S A := by
  apply wsubsets_survives_deletion hB S hS
  rw [Finset.card_sdiff]
  have hinter : (S ∩ B).card ≤ t :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
  omega

private theorem block_support_family
    {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (w t k : ℕ)
    (hblock : ∀ B ∈ blocks, B.card = k)
    (hk : k = w + t)
    (hpairs : ∀ ⦃B B' : Finset V⦄, B ∈ blocks → B' ∈ blocks → B ≠ B' →
      (B ∩ B').card ≤ 1) :
    let I := {B // B ∈ blocks}
    let P : I → Finset (Finset V) := fun B => WSubsets B.1 w
    (∀ i A, A ∈ P i → A.card = w) ∧
    (∀ i S, S.card = t → ∃ A ∈ P i, Disjoint S A) ∧
    (∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ A' ∈ P j,
      (A ∩ A').card ≤ 1) := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro i A hA
    exact wsubsets_mem_size hA
  · intro i S hS
    apply wsubsets_deletion_of_block_size (hblock i.1 i.2 ▸ hk ▸ rfl) S hS
  · intro i j hij A hA A' hA'
    have hblocks : i.1 ≠ j.1 := by
      intro hEq
      exact hij (Subtype.ext hEq)
    have hsub : A ∩ A' ⊆ ((i.val : Finset V) ∩ (j.val : Finset V)) := by
      intro v hv
      have hv' := Finset.mem_inter.mp hv
      exact Finset.mem_inter.mpr
        ⟨wsubsets_mem_subset hA hv'.1, wsubsets_mem_subset hA' hv'.2⟩
    exact (Finset.card_le_card hsub).trans (hpairs i.2 j.2 hblocks)


/-- The leave bound is attained whenever a finite design with the same parameters is supplied. -/
theorem finite_cpecc_support_optimum_of_design
    {V : Type*} [Fintype V] [DecidableEq V]
    (n w t g k : ℕ)
    (hn : Fintype.card V = n) (hkdef : k = w + t) (hkN : k ≤ n)
    (ht : 1 ≤ t) (hw : t + 3 < w) (hg : 1 ≤ g) (hgw : g < w)
    (hRdiv : k - 1 ∣ n - g) (hJdiv : k * (k - 1) ∣ n * (n - g))
    (hthreshold : k * (k + g - 2) ≤ 2 * AppendixA.B w t)
    (G : GroupDivisibleDesign V k g) :
    IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset V), IsSupportFamily P w t}
      (n * (n - g) / (k * (k - 1))) := by
  classical
  let J := n * (n - g) / (k * (k - 1))
  have hcount : G.blocks.card = J := by
    simpa [J, hn] using design_block_count G (by omega)
  let I := {B // B ∈ G.blocks}
  have hI : Fintype.card I = J := (Fintype.card_coe G.blocks).trans hcount
  let e : I ≃ Fin J := Fintype.equivFinOfCardEq hI
  obtain ⟨hsize, hdel, hcross⟩ :=
    block_support_family G.blocks w t k G.block_card hkdef (design_blocks_inter_le_one G)
  refine ⟨⟨fun i => WSubsets (e.symm i).1 w, ?_⟩, ?_⟩
  · refine ⟨fun i => hsize (e.symm i), fun i => hdel (e.symm i), ?_⟩
    intro i j hij
    exact hcross (fun h => hij (e.symm.injective h))
  · rintro m ⟨P, hPsize, hPdel, hPcross⟩
    simpa using finite_cpecc_support_upper_bound P n w t g k
      hn hkdef hkN ht hw hg hgw hRdiv hJdiv hPsize hPdel hPcross hthreshold

end CPECCBridge
