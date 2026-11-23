/- GID: D5/S3/Combinatorics/WeightedBond/FiniteOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WeightedBond/FiniteOrder
   mirror-E: none(waiver:kernel-checked-source-model)
   anchors: []
   utility: none
   digest: Finite colored connected-block refinement and the product of literal lower intervals. -/

import D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Pi.Interval

/-! The finite-color carrier and rank-marked Möbius polynomial of
González D’León and Wachs, arXiv:2608.08692v2, §5.1 and §7.1. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.WeightedBond

open Finset
open D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource
  (children connectedWeightedBottom children_self parentBlock parentBlock_mem_children children_parent_fiber)

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each actual block is connected in isolation and has a weak composition of
its cardinality minus one. Each coordinate is bounded by the ambient cardinality.
Weights off the actual blocks have a unique zero representation. -/
structure MultiweightedBond (r : ℕ) (G : SimpleGraph V) where
  partition : Finpartition (univ : Finset V)
  weight : Finset V → Fin r → Fin (Fintype.card V + 1)
  weight_sum : ∀ B ∈ partition.parts, (∑ c, (weight B c : ℕ)) = B.card - 1
  weight_off : ∀ B ∉ partition.parts, ∀ c, weight B c = 0
  connected : ∀ B ∈ partition.parts, (G.induce (B : Set V)).Connected

namespace MultiweightedBond

variable {r : ℕ} {G : SimpleGraph V}

private theorem data_injective :
    Function.Injective (fun P : MultiweightedBond r G => (P.partition, P.weight)) := by
  rintro ⟨p, w, hs, hz, hc⟩ ⟨q, v, hs', hz', hc'⟩ h
  change (p, w) = (q, v) at h
  cases h
  rfl

instance : DecidableEq (MultiweightedBond r G) := data_injective.decidableEq

noncomputable instance : Fintype (MultiweightedBond r G) :=
  Fintype.ofInjective _ data_injective

theorem ext_weights {P Q : MultiweightedBond r G} (hp : P.partition = Q.partition)
    (hw : ∀ B ∈ P.partition.parts, ∀ c, P.weight B c = Q.weight B c) : P = Q := by
  apply data_injective
  refine Prod.ext hp ?_
  funext B c
  change P.weight B c = Q.weight B c
  by_cases hb : B ∈ P.partition.parts
  · exact hw B hb c
  · rw [P.weight_off B hb, Q.weight_off B (hp ▸ hb)]

def childSum (P : MultiweightedBond r G) (B : Finset V) (c : Fin r) : ℕ :=
  ∑ A ∈ children P.partition B, (P.weight A.val c : ℕ)

def Refines (P Q : MultiweightedBond r G) : Prop :=
  P.partition ≤ Q.partition ∧
    ∀ B : Q.partition.parts, ∀ c, childSum P B.val c ≤ (Q.weight B.val c : ℕ)

instance : LE (MultiweightedBond r G) := ⟨Refines⟩

private theorem childSum_self (P : MultiweightedBond r G) (B : P.partition.parts)
    (c : Fin r) : childSum P B.val c = (P.weight B.val c : ℕ) := by
  rw [childSum, children_self, sum_singleton]

private theorem childSum_decompose (P Q R : MultiweightedBond r G)
    (hPQ : P.partition ≤ Q.partition) (hQR : Q.partition ≤ R.partition)
    (B : R.partition.parts) (c : Fin r) :
    childSum P B.val c =
      ∑ A ∈ children Q.partition B.val, childSum P A.val c := by
  classical
  symm
  calc
    _ = ∑ A ∈ children Q.partition B.val,
          ∑ D ∈ (children P.partition B.val).filter (fun D => parentBlock hPQ D = A),
            (P.weight D.val c : ℕ) := by
      apply sum_congr rfl
      intro A hA
      rw [children_parent_fiber hPQ B hA]
      rfl
    _ = _ := sum_fiberwise_of_maps_to
      (fun _ hD => parentBlock_mem_children hPQ hQR B hD) _

instance : PartialOrder (MultiweightedBond r G) where
  le_refl P := ⟨le_rfl, fun B c => (childSum_self P B c).le⟩
  le_trans P Q R hPQ hQR := by
    change Refines P Q at hPQ
    change Refines Q R at hQR
    refine ⟨hPQ.1.trans hQR.1, fun B c => ?_⟩
    rw [childSum_decompose P Q R hPQ.1 hQR.1 B c]
    exact (sum_le_sum fun A _ => hPQ.2 A c).trans (hQR.2 B c)
  le_antisymm P Q hPQ hQP := by
    change Refines P Q at hPQ
    change Refines Q P at hQP
    have hp := le_antisymm hPQ.1 hQP.1
    apply ext_weights hp
    intro B hB c
    have hBQ : B ∈ Q.partition.parts := hp ▸ hB
    have hp1 := hPQ.2 ⟨B, hBQ⟩ c
    have hp2 := hQP.2 ⟨B, hB⟩ c
    change childSum P B c ≤ _ at hp1
    change childSum Q B c ≤ _ at hp2
    rw [childSum_self P ⟨B, hB⟩ c] at hp1
    rw [childSum_self Q ⟨B, hBQ⟩ c] at hp2
    exact Fin.ext (le_antisymm hp1 hp2)

def singletonZero (r : ℕ) (G : SimpleGraph V) : MultiweightedBond r G where
  partition := ⊥
  weight := fun _ _ => 0
  weight_sum := by
    intro B hB
    obtain ⟨v, _, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    simp
  weight_off := by simp
  connected := (connectedWeightedBottom G).property

instance : OrderBot (MultiweightedBond r G) where
  bot := singletonZero r G
  bot_le P := by
    change Refines (singletonZero r G) P
    refine ⟨bot_le, fun B c => ?_⟩
    simp [childSum, singletonZero]

noncomputable instance : LocallyFiniteOrder (MultiweightedBond r G) := by
  classical
  exact Fintype.toLocallyFiniteOrder

theorem complete_block_connected (P : Finpartition (univ : Finset V)) {B : Finset V}
    (hB : B ∈ P.parts) : ((SimpleGraph.completeGraph V).induce (B : Set V)).Connected := by
  rw [SimpleGraph.induce_top, SimpleGraph.connected_top_iff]
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr (P.ne_bot hB)
  exact ⟨⟨v, hv⟩⟩

theorem weight_eq_zero_of_card_one (P : MultiweightedBond r G) {B : Finset V}
    (hB : B ∈ P.partition.parts) (hcard : B.card = 1) (c : Fin r) :
    P.weight B c = 0 := by
  have hs := P.weight_sum B hB
  rw [hcard] at hs
  have hc : (P.weight B c : ℕ) ≤ ∑ j, (P.weight B j : ℕ) :=
    single_le_sum (f := fun j => (P.weight B j : ℕ))
      (fun _ _ => Nat.zero_le _) (mem_univ c)
  apply Fin.ext
  simpa [hs] using hc

/-- The equal-variable monomial has degree the number of vertices minus
the number of blocks. -/
theorem total_weight_eq_rank (P : MultiweightedBond r G) :
    (∑ B ∈ P.partition.parts, ∑ c, (P.weight B c : ℕ)) =
      Fintype.card V - P.partition.parts.card := by
  apply Nat.eq_sub_of_add_eq
  calc
    _ = ∑ B ∈ P.partition.parts, ((∑ c, (P.weight B c : ℕ)) + 1) := by
      rw [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, mul_one]
    _ = ∑ B ∈ P.partition.parts, B.card := by
      apply sum_congr rfl
      intro B hB
      rw [P.weight_sum B hB]
      exact Nat.sub_add_cancel (Finset.nonempty_iff_ne_empty.mpr (P.partition.ne_bot hB)).card_pos
    _ = _ := by simpa using P.partition.sum_card_parts

end MultiweightedBond

abbrev CompleteBond (n r : ℕ) :=
  MultiweightedBond r (SimpleGraph.completeGraph (Fin n))

def psiComplete (n r : ℕ) : Polynomial ℚ :=
  ∑ P : CompleteBond n r,
    Polynomial.C (((IncidenceAlgebra.mu ℤ) (⊥ : CompleteBond n r) P : ℤ) : ℚ) *
      Polynomial.X ^ (n - P.partition.parts.card)

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false

namespace D5.S3.Combinatorics.WeightedBond.MultiweightedBond

open Finset
open D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource (children parentBlock parentBlock_eq_of_subset)

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {G : SimpleGraph V}

private def ambient (B : Finset V) (A : Finset (B : Set V)) : Finset V :=
  A.map (Function.Embedding.subtype _)

omit [Fintype V] [DecidableEq V] in
private theorem ambient_injective (B : Finset V) : Function.Injective (ambient B) :=
  Finset.map_injective _

omit [Fintype V] [DecidableEq V] in
private theorem ambient_subset_block {B : Finset V} (A : Finset (B : Set V)) :
    ambient B A ⊆ B :=
  fun _ hx => A.property_of_mem_map_subtype hx

omit [Fintype V] [DecidableEq V] in
private theorem ambient_subset {B : Finset V} {A D : Finset (B : Set V)} :
    ambient B A ⊆ ambient B D ↔ A ⊆ D :=
  Finset.map_subset_map

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem card_ambient (B : Finset V) (A : Finset (B : Set V)) :
    (ambient B A).card = A.card := Finset.card_map _

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem ambient_univ (B : Finset V) :
    ambient B univ = B := by
  ext x
  simp [ambient, Finset.mem_map]

omit [Fintype V] in
private theorem ambient_subtype {B A : Finset V} (h : A ⊆ B) :
    ambient B (A.subtype (· ∈ B)) = A := Finset.subtype_map_of_mem h

omit [Fintype V] [DecidableEq V] in
private theorem mem_ambient {B : Finset V} {A : Finset (B : Set V)} (x : B) :
    x.val ∈ ambient B A ↔ x ∈ A := Finset.mem_map' _

omit [Fintype V] in
private theorem mem_pull_parts {B : Finset V} (P : Finpartition B)
    (A : Finset (B : Set V)) :
    A ∈ P.parts.image (fun D => D.subtype (· ∈ B)) ↔ ambient B A ∈ P.parts := by
  constructor
  · intro h
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp h
    simpa only [ambient_subtype (P.subset hD)] using hD
  · intro h
    refine Finset.mem_image.mpr ⟨ambient B A, h, ambient_injective B ?_⟩
    exact ambient_subtype (ambient_subset_block A)

private def pullPartition {B : Finset V} (P : Finpartition B) :
    Finpartition (univ : Finset (B : Set V)) := by
  classical
  refine Finpartition.ofExistsUnique (P.parts.image (fun D => D.subtype (· ∈ B)))
    (fun A _ => subset_univ A) ?_ ?_
  · intro x _
    obtain ⟨D, ⟨hD, hx⟩, huniq⟩ := P.existsUnique_mem x.property
    let A := D.subtype (· ∈ B)
    have hA : ambient B A = D := ambient_subtype (P.subset hD)
    refine ⟨A, ⟨Finset.mem_image.mpr ⟨D, hD, rfl⟩, (mem_ambient x).mp (hA ▸ hx)⟩, ?_⟩
    rintro A' ⟨hA', hx'⟩
    apply ambient_injective B
    exact (huniq _ ⟨(mem_pull_parts P A').mp hA', (mem_ambient x).mpr hx'⟩).trans hA.symm
  · intro h
    apply P.empty_notMem_parts
    exact (mem_pull_parts P ∅).mp h

omit [Fintype V] in
@[simp] private theorem mem_pullPartition {B : Finset V} (P : Finpartition B)
    (A : Finset (B : Set V)) : A ∈ (pullPartition P).parts ↔ ambient B A ∈ P.parts :=
  mem_pull_parts P A

private def pushPartition (B : Finset V) (P : Finpartition (univ : Finset (B : Set V))) :
    Finpartition B := by
  classical
  refine Finpartition.ofExistsUnique (P.parts.image (ambient B)) ?_ ?_ ?_
  · intro A hA
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hA
    exact ambient_subset_block D
  · intro x hx
    let y : B := ⟨x, hx⟩
    obtain ⟨D, ⟨hD, hy⟩, huniq⟩ := P.existsUnique_mem (Finset.mem_univ y)
    refine ⟨ambient B D, ⟨Finset.mem_image.mpr ⟨D, hD, rfl⟩, (mem_ambient y).mpr hy⟩, ?_⟩
    rintro A ⟨hA, hxA⟩
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hA
    exact congrArg (ambient B) (huniq _ ⟨hD', (mem_ambient y).mp hxA⟩)
  · intro h
    obtain ⟨D, hD, he⟩ := Finset.mem_image.mp h
    exact P.empty_notMem_parts ((ambient_injective B (show ambient B D = ambient B ∅ from he)) ▸ hD)

omit [Fintype V] in
private theorem mem_pushPartition {B A : Finset V}
    (P : Finpartition (univ : Finset (B : Set V))) :
    A ∈ (pushPartition B P).parts ↔ ∃ D ∈ P.parts, ambient B D = A :=
  Finset.mem_image

omit [Fintype V] in
@[simp] private theorem ambient_mem_pushPartition {B : Finset V}
    (P : Finpartition (univ : Finset (B : Set V))) (A : Finset (B : Set V)) :
    ambient B A ∈ (pushPartition B P).parts ↔ A ∈ P.parts := by
  rw [mem_pushPartition]
  exact ⟨fun ⟨D, hD, h⟩ => (ambient_injective B h) ▸ hD, fun h => ⟨A, h, rfl⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem connected_ambient_iff (B : Finset V) (A : Finset (B : Set V)) :
    (G.induce (ambient B A : Set V)).Connected ↔
      ((G.induce (B : Set V)).induce (A : Set (B : Set V))).Connected := by
  let e : ((G.induce (B : Set V)).induce (A : Set (B : Set V))) ≃g
      G.induce (ambient B A : Set V) :=
    { toFun := fun x => ⟨x.val.val, (mem_ambient x.val).mpr x.property⟩
      invFun := fun x =>
        let y : B := ⟨x.val, ambient_subset_block A x.property⟩
        ⟨y, (mem_ambient y).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.connected_iff.symm

private theorem mem_restrict_of_refines {P Q : Finpartition (univ : Finset V)}
    (h : P ≤ Q) (B : Q.parts) (A : Finset V) :
    A ∈ (P.restrict (Q.le B.property)).parts ↔ A ∈ P.parts ∧ A ⊆ B.val := by
  rw [Finpartition.parts_restrict, mem_erase, mem_image]
  constructor
  · rintro ⟨hne, D, hD, rfl⟩
    obtain ⟨C, hC, hDC⟩ := h hD
    have hCB : C = B.val := Q.disjoint.elim hC B.property (by
      intro hd
      exact hne (le_bot_iff.mp (inf_le_inf_right B.val hDC |>.trans hd.le_bot)))
    have hDB : D ⊆ B.val := hCB ▸ hDC
    rw [inf_eq_left.mpr hDB]
    exact ⟨hD, hDB⟩
  · rintro ⟨hA, hAB⟩
    exact ⟨P.ne_bot hA, A, hA, inf_eq_left.mpr hAB⟩

private theorem weight_le_card (P : MultiweightedBond r G) {A : Finset V}
    (hA : A ∈ P.partition.parts) (c : Fin r) : (P.weight A c : ℕ) ≤ A.card := by
  calc
    (P.weight A c : ℕ) ≤ ∑ j, (P.weight A j : ℕ) :=
      single_le_sum (f := fun j => (P.weight A j : ℕ)) (fun _ _ => Nat.zero_le _) (mem_univ c)
    _ = A.card - 1 := P.weight_sum A hA
    _ ≤ A.card := Nat.sub_le _ _

variable {π P Q : MultiweightedBond r G}

/-- Restrict an underlying refinement to one upper block, keeping each color coordinate. -/
def restrictBlock (P : MultiweightedBond r G) {π : MultiweightedBond r G}
    (h : P.partition ≤ π.partition) (B : π.partition.parts) :
    MultiweightedBond r (G.induce (B.val : Set V)) where
  partition := pullPartition (P.partition.restrict (π.partition.le B.property))
  weight A c := ⟨P.weight (ambient B.val A) c, by
    by_cases hA : ambient B.val A ∈ P.partition.parts
    · have hw := weight_le_card P hA c
      rw [card_ambient] at hw
      exact Nat.lt_succ_of_le (hw.trans (Finset.card_le_univ A))
    · rw [P.weight_off _ hA c]
      exact Nat.zero_lt_succ _⟩
  weight_sum A hA := by
    have hm := (mem_restrict_of_refines h B _).mp ((mem_pullPartition _ A).mp hA)
    simpa only [card_ambient] using P.weight_sum _ hm.1
  weight_off A hA c := by
    apply Fin.ext
    change (P.weight (ambient B.val A) c : ℕ) = 0
    rw [P.weight_off _ (fun hm => hA ((mem_pullPartition _ A).mpr
      ((mem_restrict_of_refines h B _).mpr ⟨hm, ambient_subset_block A⟩))) c]
    rfl
  connected A hA := by
    have hm := (mem_restrict_of_refines h B _).mp ((mem_pullPartition _ A).mp hA)
    exact (connected_ambient_iff B.val A).mp (P.connected _ hm.1)

@[simp] private theorem mem_restrictBlock (h : P.partition ≤ π.partition)
    (B : π.partition.parts) (A : Finset (B.val : Set V)) :
    A ∈ (restrictBlock P h B).partition.parts ↔ ambient B.val A ∈ P.partition.parts := by
  rw [restrictBlock, mem_pullPartition, mem_restrict_of_refines h B]
  exact and_iff_left (ambient_subset_block A)

@[simp] private theorem restrictBlock_weight (h : P.partition ≤ π.partition)
    (B : π.partition.parts) (A : Finset (B.val : Set V)) (c : Fin r) :
    ((restrictBlock P h B).weight A c : ℕ) = P.weight (ambient B.val A) c := rfl

/-- The one-block bond on the induced graph, with the upper block's original weights. -/
def oneBlock (π : MultiweightedBond r G) (B : π.partition.parts) :
    MultiweightedBond r (G.induce (B.val : Set V)) :=
  restrictBlock π le_rfl B

theorem oneBlock_parts (π : MultiweightedBond r G) (B : π.partition.parts) :
    (oneBlock π B).partition.parts = {univ} := by
  ext A
  rw [oneBlock, mem_restrictBlock, mem_singleton]
  constructor
  · intro hA
    have he := π.partition.disjoint.eq_of_le hA B.property
      (π.partition.ne_bot hA) (ambient_subset_block A)
    exact ambient_injective B.val (he.trans (ambient_univ B.val).symm)
  · rintro rfl
    simpa only [ambient_univ] using B.property

theorem oneBlock_weight (π : MultiweightedBond r G) (B : π.partition.parts) (c : Fin r) :
    ((oneBlock π B).weight univ c : ℕ) = π.weight B.val c := by
  change (π.weight (ambient B.val univ) c : ℕ) = _
  rw [ambient_univ]


private theorem mem_children {W : Type*} [Fintype W] [DecidableEq W]
    {p : Finpartition (univ : Finset W)} {A : p.parts} {D : Finset W} :
    A ∈ children p D ↔ A.val ⊆ D := by
  simp [children]

private theorem restrictBlock_childSum (h : P.partition ≤ π.partition)
    (B : π.partition.parts) (D : Finset (B.val : Set V)) (c : Fin r) :
    (restrictBlock P h B).childSum D c = P.childSum (ambient B.val D) c := by
  classical
  rw [childSum, childSum]
  let push (A : (restrictBlock P h B).partition.parts) : P.partition.parts :=
    ⟨ambient B.val A.val, (mem_restrictBlock h B A.val).mp A.property⟩
  refine Finset.sum_bij (fun A _ => push A) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro A hA
    exact mem_children.mpr (ambient_subset.mpr (mem_children.mp hA))
  · intro A _ A' _ he
    exact Subtype.ext (ambient_injective B.val (congrArg Subtype.val he))
  · intro A hA
    have hsub := (mem_children.mp hA).trans (ambient_subset_block D)
    let D' := A.val.subtype (· ∈ B.val)
    have he : ambient B.val D' = A.val := ambient_subtype hsub
    let A' : (restrictBlock P h B).partition.parts :=
      ⟨D', (mem_restrictBlock h B D').mpr (he.symm ▸ A.property)⟩
    refine ⟨A', mem_children.mpr (ambient_subset.mp ?_), Subtype.ext he⟩
    exact he.symm ▸ mem_children.mp hA

private theorem refines_iff_restrictBlock (hP : P.partition ≤ π.partition)
    (hQ : Q.partition ≤ π.partition) :
    P ≤ Q ↔ ∀ B : π.partition.parts, restrictBlock P hP B ≤ restrictBlock Q hQ B := by
  change Refines P Q ↔
    ∀ B : π.partition.parts, Refines (restrictBlock P hP B) (restrictBlock Q hQ B)
  constructor
  · rintro ⟨hpq, hw⟩ B
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨D, hD, hAD⟩ := hpq ((mem_restrictBlock hP B _).mp hA)
      let pA : P.partition.parts := ⟨ambient B.val A, (mem_restrictBlock hP B _).mp hA⟩
      let qD : Q.partition.parts := ⟨D, hD⟩
      have he := parentBlock_eq_of_subset hP pA B (ambient_subset_block A)
      have hparent := parentBlock_eq_of_subset hP pA (parentBlock hQ qD)
        (hAD.trans (hQ hD).choose_spec.2)
      have hDB : D ⊆ B.val := by
        have he' : parentBlock hQ qD = B := hparent.symm.trans he
        exact he' ▸ (hQ hD).choose_spec.2
      let D' := D.subtype (· ∈ B.val)
      have hD' : ambient B.val D' = D := ambient_subtype hDB
      refine ⟨D', (mem_restrictBlock hQ B D').mpr (hD'.symm ▸ hD), ambient_subset.mp ?_⟩
      exact hD'.symm ▸ hAD
    · intro D c
      rw [restrictBlock_childSum, restrictBlock_weight]
      exact hw ⟨ambient B.val D.val, (mem_restrictBlock hQ B _).mp D.property⟩ c
  · intro h
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨B, hB, hAB⟩ := hP hA
      let b : π.partition.parts := ⟨B, hB⟩
      let A' := A.subtype (· ∈ B)
      have hAmbient : ambient B A' = A := ambient_subtype hAB
      have hA' : A' ∈ (restrictBlock P hP b).partition.parts :=
        (mem_restrictBlock hP b A').mpr (hAmbient.symm ▸ hA)
      obtain ⟨D, hD, hAD⟩ := (h b).1 hA'
      exact ⟨ambient B D, (mem_restrictBlock hQ b D).mp hD,
        hAmbient ▸ ambient_subset.mpr hAD⟩
    · intro D c
      obtain ⟨B, hB, hDB⟩ := hQ D.property
      let b : π.partition.parts := ⟨B, hB⟩
      let D' := D.val.subtype (· ∈ B)
      have hAmbient : ambient B D' = D.val := ambient_subtype hDB
      have hD' : D' ∈ (restrictBlock Q hQ b).partition.parts :=
        (mem_restrictBlock hQ b D').mpr (hAmbient.symm ▸ D.property)
      have hw := (h b).2 ⟨D', hD'⟩ c
      rw [restrictBlock_childSum, restrictBlock_weight] at hw
      change P.childSum (ambient B D') c ≤ (Q.weight (ambient B D') c : ℕ) at hw
      rwa [hAmbient] at hw

private abbrev BlockBonds (π : MultiweightedBond r G) :=
  (B : π.partition.parts) → MultiweightedBond r (G.induce (B.val : Set V))

private def combinePartition (π : MultiweightedBond r G) (f : BlockBonds π) :
    Finpartition (univ : Finset V) :=
  π.partition.bind fun B hB => pushPartition B (f ⟨B, hB⟩).partition

private theorem combinePartition_le (π : MultiweightedBond r G) (f : BlockBonds π) :
    combinePartition π f ≤ π.partition := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := Finpartition.mem_bind.mp hA
  exact ⟨B, hB, (pushPartition B (f ⟨B, hB⟩).partition).subset hAB⟩

private theorem local_mem_combinePartition (f : BlockBonds π) (B : π.partition.parts)
    {A : Finset (B.val : Set V)} (hA : A ∈ (f B).partition.parts) :
    ambient B.val A ∈ (combinePartition π f).parts :=
  Finpartition.mem_bind.mpr ⟨B.val, B.property, (ambient_mem_pushPartition _ A).mpr hA⟩

private theorem mem_local_of_mem_combinePartition (f : BlockBonds π) (B : π.partition.parts)
    {A : Finset (B.val : Set V)} (hA : ambient B.val A ∈ (combinePartition π f).parts) :
    A ∈ (f B).partition.parts := by
  obtain ⟨C, hC, hAC⟩ := Finpartition.mem_bind.mp hA
  have hsub := (pushPartition C (f ⟨C, hC⟩).partition).subset hAC
  let lower : (combinePartition π f).parts := ⟨ambient B.val A, hA⟩
  have hb := parentBlock_eq_of_subset (combinePartition_le π f) lower B (ambient_subset_block A)
  have hc := parentBlock_eq_of_subset (combinePartition_le π f) lower ⟨C, hC⟩ hsub
  have he : (⟨C, hC⟩ : π.partition.parts) = B := hc.symm.trans hb
  have hAC' : ambient B.val A ∈ (pushPartition B.val (f B).partition).parts :=
    he ▸ hAC
  exact (ambient_mem_pushPartition _ A).mp hAC'

private def localPart (f : BlockBonds π) (A : (combinePartition π f).parts) :
    Finset ((parentBlock (combinePartition_le π f) A).val : Set V) :=
  A.val.subtype (· ∈ (parentBlock (combinePartition_le π f) A).val)

private theorem ambient_localPart (f : BlockBonds π) (A : (combinePartition π f).parts) :
    ambient (parentBlock (combinePartition_le π f) A).val (localPart f A) = A.val :=
  ambient_subtype ((combinePartition_le π f A.property).choose_spec.2)

private theorem localPart_mem (f : BlockBonds π) (A : (combinePartition π f).parts) :
    localPart f A ∈ (f (parentBlock (combinePartition_le π f) A)).partition.parts :=
  mem_local_of_mem_combinePartition f _
    ((ambient_localPart f A).symm ▸ A.property)

/-- Recombine the local bonds by juxtaposing the literal subpartitions. -/
def recombineBlocks (π : MultiweightedBond r G) (f : BlockBonds π) :
    MultiweightedBond r G where
  partition := combinePartition π f
  weight A c := if hA : A ∈ (combinePartition π f).parts then
    let B := parentBlock (combinePartition_le π f) ⟨A, hA⟩
    let D := localPart f ⟨A, hA⟩
    ⟨(f B).weight D c, by
      have hw := weight_le_card (f B) (localPart_mem f ⟨A, hA⟩) c
      have he : D.card = A.card :=
        (card_ambient B.val D).symm.trans (congrArg Finset.card (ambient_localPart f ⟨A, hA⟩))
      rw [he] at hw
      exact Nat.lt_succ_of_le (hw.trans (card_le_univ A))⟩
    else 0
  weight_sum A hA := by
    simp only [dite_eq_left hA]
    let B := parentBlock (combinePartition_le π f) ⟨A, hA⟩
    let D := localPart f ⟨A, hA⟩
    have hw := (f B).weight_sum D (localPart_mem f ⟨A, hA⟩)
    have he : D.card = A.card :=
      (card_ambient B.val D).symm.trans (congrArg Finset.card (ambient_localPart f ⟨A, hA⟩))
    exact hw.trans (congrArg (· - 1) he)
  weight_off A hA _ := dite_eq_right hA
  connected A hA := by
    let B := parentBlock (combinePartition_le π f) ⟨A, hA⟩
    let D := localPart f ⟨A, hA⟩
    have hc := (connected_ambient_iff (G := G) B.val D).mpr
      ((f B).connected D (localPart_mem f ⟨A, hA⟩))
    have he : ambient B.val D = A := ambient_localPart f ⟨A, hA⟩
    rwa [he] at hc

private theorem recombineBlocks_weight (f : BlockBonds π) (B : π.partition.parts)
    {A : Finset (B.val : Set V)} (hA : A ∈ (f B).partition.parts) (c : Fin r) :
    ((recombineBlocks π f).weight (ambient B.val A) c : ℕ) = (f B).weight A c := by
  have hmem := local_mem_combinePartition f B hA
  let lower : (combinePartition π f).parts := ⟨ambient B.val A, hmem⟩
  have hparent := parentBlock_eq_of_subset (combinePartition_le π f) lower B
    (ambient_subset_block A)
  have reindex (C : π.partition.parts) (he : parentBlock (combinePartition_le π f) lower = C) :
      let D := (ambient B.val A).subtype (· ∈ C.val)
      ((f (parentBlock (combinePartition_le π f) lower)).weight (localPart f lower) c : ℕ) =
        (f C).weight D c := by
    subst C
    rfl
  have hD : (ambient B.val A).subtype (· ∈ B.val) = A :=
    ambient_injective B.val (ambient_subtype (ambient_subset_block A))
  simp only [recombineBlocks, dite_eq_left hmem]
  change ((f (parentBlock (combinePartition_le π f) lower)).weight (localPart f lower) c : ℕ) = _
  exact (reindex B hparent).trans (congrArg (fun D => ((f B).weight D c : ℕ)) hD)

theorem restrictBlock_recombineBlocks (π : MultiweightedBond r G) (f : BlockBonds π)
    (B : π.partition.parts) :
    restrictBlock (recombineBlocks π f) (combinePartition_le π f) B = f B := by
  apply ext_weights
  · apply Finpartition.ext
    ext A
    exact (mem_restrictBlock (P := recombineBlocks π f) (combinePartition_le π f) B A).trans
      ⟨mem_local_of_mem_combinePartition f B, local_mem_combinePartition f B⟩
  · intro A hA c
    apply Fin.ext
    have hmem := (mem_restrictBlock (P := recombineBlocks π f) (combinePartition_le π f) B A).mp hA
    exact recombineBlocks_weight f B (mem_local_of_mem_combinePartition f B hmem) c

theorem recombineBlocks_restrictBlock (P : MultiweightedBond r G)
    (h : P.partition ≤ π.partition) :
    recombineBlocks π (restrictBlock P h) = P := by
  apply ext_weights
  · apply Finpartition.ext
    ext A
    change A ∈ (combinePartition π (restrictBlock P h)).parts ↔ _
    rw [combinePartition, Finpartition.mem_bind]
    constructor
    · rintro ⟨B, hB, hA⟩
      obtain ⟨D, hD, rfl⟩ := mem_pushPartition _ |>.mp hA
      exact (mem_restrictBlock h ⟨B, hB⟩ D).mp hD
    · intro hA
      obtain ⟨B, hB, hAB⟩ := h hA
      let D := A.subtype (· ∈ B)
      have hD : ambient B D = A := ambient_subtype hAB
      exact ⟨B, hB, (mem_pushPartition _).mpr
        ⟨D, (mem_restrictBlock h ⟨B, hB⟩ D).mpr (hD.symm ▸ hA), hD⟩⟩
  · intro A hA c
    change A ∈ (combinePartition π (restrictBlock P h)).parts at hA
    obtain ⟨B, hB, hAB⟩ := Finpartition.mem_bind.mp hA
    obtain ⟨D, hD, rfl⟩ := mem_pushPartition _ |>.mp hAB
    apply Fin.ext
    exact (recombineBlocks_weight (restrictBlock P h) ⟨B, hB⟩ hD c).trans
      (restrictBlock_weight h ⟨B, hB⟩ D c)

/-- The lower interval of a connected finite-colored weighted partition factors over its blocks. -/
def lowerIntervalOrderIso (π : MultiweightedBond r G) :
    Set.Iic π ≃o ((B : π.partition.parts) → Set.Iic (oneBlock π B)) where
  toFun P B := ⟨restrictBlock P.val (show Refines P.val π from P.property).1 B,
    (refines_iff_restrictBlock (show Refines P.val π from P.property).1 le_rfl).mp P.property B⟩
  invFun f :=
    let g : BlockBonds π := fun B => (f B).val
    ⟨recombineBlocks π g, (refines_iff_restrictBlock (combinePartition_le π g) le_rfl).mpr
      (fun B => by rw [restrictBlock_recombineBlocks]; exact (f B).property)⟩
  left_inv P := Subtype.ext (recombineBlocks_restrictBlock P.val (show Refines P.val π from P.property).1)
  right_inv f := funext (fun B => Subtype.ext (restrictBlock_recombineBlocks π _ B))
  map_rel_iff' := by
    intro P Q
    exact (refines_iff_restrictBlock (show Refines P.val π from P.property).1
      (show Refines Q.val π from Q.property).1).symm


/-- The ambient exponent `|V| - number of blocks` is the sum of the block exponents. -/
theorem rank_eq_sum_block_ranks (π : MultiweightedBond r G) (P : Set.Iic π) :
    Fintype.card V - P.val.partition.parts.card =
      ∑ B : π.partition.parts,
        (Fintype.card (B.val : Set V) -
          ((lowerIntervalOrderIso π P B).val.partition.parts.card)) := by
  classical
  let h := (show Refines P.val π from P.property).1
  let f := restrictBlock P.val h
  have hparts : P.val.partition.parts.card =
      ∑ B : π.partition.parts, (f B).partition.parts.card := by
    calc
      _ = (combinePartition π f).parts.card :=
        congrArg (fun x : MultiweightedBond r G => x.partition.parts.card)
          (recombineBlocks_restrictBlock P.val h).symm
      _ = ∑ B ∈ π.partition.parts.attach, (pushPartition B.val (f B).partition).parts.card :=
        Finpartition.card_bind _
      _ = _ := by
        simp only [Finset.attach_eq_univ]
        apply Finset.sum_congr rfl
        intro B _
        change ((f B).partition.parts.image (ambient B.val)).card = _
        exact Finset.card_image_of_injective _ (ambient_injective B.val)
  have hcards : (∑ B : π.partition.parts, Fintype.card (B.val : Set V)) = Fintype.card V := by
    calc
      _ = ∑ B : π.partition.parts, B.val.card := by
        exact Finset.sum_congr rfl fun B _ => Fintype.card_coe B.val
      _ = ∑ B ∈ π.partition.parts, B.card := by
        rw [← Finset.attach_eq_univ, Finset.sum_attach]
      _ = _ := by simpa only [Finset.card_univ] using π.partition.sum_card_parts
  change _ = ∑ B : π.partition.parts, (Fintype.card (B.val : Set V) - (f B).partition.parts.card)
  symm
  apply Nat.eq_sub_of_add_eq
  rw [hparts, ← Finset.sum_add_distrib, ← hcards]
  exact Finset.sum_congr rfl fun B _ => Nat.sub_add_cancel (by
    simpa only [Finset.card_univ] using (f B).partition.card_parts_le_card)

open IncidenceAlgebra (mu sum_Icc_mu_right)
open scoped Classical

private theorem mu_bot_unique {α : Type*} [PartialOrder α] [OrderBot α]
    [LocallyFiniteOrder α] [DecidableEq α] (f : α → ℤ)
    (hf : ∀ x, ∑ y ∈ Icc (⊥ : α) x, f y = if ⊥ = x then 1 else 0) (x : α) :
    mu ℤ (⊥ : α) x = f x := by
  induction x using (measure (fun z : α => (Icc (⊥ : α) z).card)).wf.induction with
  | h x ih =>
    have hs := (sum_Icc_mu_right (𝕜 := ℤ) (⊥ : α) x).trans (hf x).symm
    rw [Icc_eq_cons_Ico bot_le, sum_cons, sum_cons] at hs
    have hsum : (∑ y ∈ Ico (⊥ : α) x, mu ℤ (⊥ : α) y) = ∑ y ∈ Ico (⊥ : α) x, f y := by
      apply sum_congr rfl
      intro y hy
      exact ih y (card_lt_card (Icc_ssubset_Icc_right bot_le le_rfl (mem_Ico.mp hy).2))
    rw [hsum] at hs
    exact add_right_cancel hs

theorem mu_bot_iic {α : Type*} [PartialOrder α] [OrderBot α]
    [LocallyFiniteOrder α] [DecidableEq α] (a : α) (x : Set.Iic a) :
    mu ℤ (⊥ : Set.Iic a) x = mu ℤ (⊥ : α) x.val := by
  apply mu_bot_unique (fun y : Set.Iic a => mu ℤ (⊥ : α) y.val) _ x
  intro y
  have hm := Finset.map_subtype_embedding_Icc (· ∈ Set.Iic a) (⊥ : Set.Iic a) y
    (fun _ _ _ _ hy _ ha => hy.trans ha)
  change _ = Icc (⊥ : α) y.val at hm
  calc
    _ = ∑ z ∈ (Icc (⊥ : Set.Iic a) y).map (Function.Embedding.subtype (· ∈ Set.Iic a)),
        mu ℤ (⊥ : α) z :=
      (Finset.sum_map _ (Function.Embedding.subtype (· ∈ Set.Iic a)) (mu ℤ (⊥ : α))).symm
    _ = _ := by
      rw [hm, sum_Icc_mu_right]
      have he : ((⊥ : α) = y.val) ↔ (⊥ : Set.Iic a) = y :=
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simp only [he]

theorem mu_bot_orderIso {α β : Type*} [PartialOrder α] [PartialOrder β]
    [OrderBot α] [OrderBot β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableEq α] [DecidableEq β] (e : α ≃o β) (x : α) :
    mu ℤ (⊥ : α) x = mu ℤ (⊥ : β) (e x) := by
  apply mu_bot_unique (fun y => mu ℤ (⊥ : β) (e y)) _ x
  intro y
  have hm : (Icc (⊥ : α) y).map e.toEquiv.toEmbedding = Icc (⊥ : β) (e y) := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e.toEquiv.toEmbedding w ∈ _ ↔ _
    rw [Finset.mem_map', mem_Icc, mem_Icc]
    simp only [bot_le, true_and, e.le_iff_le]
  change (∑ z ∈ Icc (⊥ : α) y, mu ℤ (⊥ : β) (e.toEquiv.toEmbedding z)) = _
  rw [← Finset.sum_map, hm, sum_Icc_mu_right, ← e.map_bot]
  simp only [e.injective.eq_iff]

private theorem mu_bot_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, OrderBot (α i)] [∀ i, LocallyFiniteOrder (α i)]
    [∀ i, DecidableEq (α i)] (x : ∀ i, α i) :
    mu ℤ (⊥ : ∀ i, α i) x = ∏ i, mu ℤ (⊥ : α i) (x i) := by
  apply mu_bot_unique (fun y => ∏ i, mu ℤ (⊥ : α i) (y i)) _ x
  intro y
  rw [Pi.Icc_eq, ← Finset.prod_univ_sum]
  simp only [Pi.bot_apply, sum_Icc_mu_right, Finset.prod_ite_zero, Finset.prod_const_one]
  have he : (∀ i ∈ (univ : Finset ι), (⊥ : α i) = y i) ↔ (⊥ : ∀ i, α i) = y :=
    ⟨fun h => funext fun i => h i (mem_univ i), fun h i _ => congrFun h i⟩
  simp only [he]

/-- The Mathlib bottom Möbius value is the product of the one-block values. -/
theorem mu_bot_eq_prod_blocks (π : MultiweightedBond r G) :
    mu ℤ (⊥ : MultiweightedBond r G) π =
      ∏ B : π.partition.parts, mu ℤ (⊥ : MultiweightedBond r (G.induce (B.val : Set V)))
        (oneBlock π B) := by
  let e := lowerIntervalOrderIso π
  have he := mu_bot_orderIso e (⊤ : Set.Iic π)
  rw [e.map_top, mu_bot_iic, mu_bot_pi] at he
  exact he.trans (Finset.prod_congr rfl fun B _ => mu_bot_iic (oneBlock π B) ⊤)

end

end D5.S3.Combinatorics.WeightedBond.MultiweightedBond
