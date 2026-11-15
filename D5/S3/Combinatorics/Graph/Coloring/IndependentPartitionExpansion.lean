/- GID: D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proper colourings as unlabelled independent partitions with injective block names. -/

/-
admission_basis: escape-witness
escape_witness: the all-palette inverse between actual Mathlib graph partitions with
injective block names and proper colourings, consumed by chromatic_expansion.
The content is an unrestricted combinatorial correspondence, not finite enumeration,
a checker, a numerical certificate, or a reduction with unfulfilled numeric premises.
decode_partition and decode_bijective: proof_shape=content; consumer=coloringEquiv
part_eq: proof_shape=bind-only; consumers=decode_partition, decode_bijective, chromatic_expansion
representative_mem: proof_shape=bind-only; consumers=decode_partition, decode_bijective,
chromatic_expansion
decode: compositional helper consumed by the new inverse construction coloringEquiv.
chromatic_expansion: proof_shape=content; source falling-factorial expansion.
All finite-sum regroupings are consumed inside that result; no application wrapper is retained.
The full-telescope source-owner Reg attempt compiles, but its audit cannot be decoded:
contract.discovery:rigid_universes. Its source and exact diagnostics are preserved externally.
The linked disclosure route is issue #30456, with the target update reserved to the caller;
source selection and binding evidence remain unfinished, with no validated registration claim.
-/

import Mathlib.Combinatorics.SimpleGraph.Partition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.CardEmbedding

/-! Unrestricted proper-colouring counts by actual unlabelled independent partitions. -/

namespace D5.S3.Combinatorics.Graph.Coloring.IndependentPartitionExpansion

open scoped BigOperators
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

private theorem part_eq (P : G.Partition) (s : P.parts) (v : V) (hv : v ∈ s.val) :
    P.toColoring v = s := by
  apply Subtype.ext
  exact Setoid.eq_of_mem_eqv_class P.isPartition.2
    (P.partOfVertex_mem v) (P.mem_partOfVertex v) s.property hv

private def representative (P : G.Partition) (s : P.parts) : V :=
  Classical.choose (Setoid.nonempty_of_mem_partition P.isPartition s.property)

private theorem representative_mem (P : G.Partition) (s : P.parts) :
    representative P s ∈ s.val := Classical.choose_spec _

/-- Give each actual nonempty block its injected palette name. -/
def decode {α : Type*} (x : Σ P : G.Partition, P.parts ↪ α) : G.Coloring α :=
  SimpleGraph.Coloring.mk (fun v => x.2 (x.1.toColoring v)) (by
    intro v w h he
    exact x.1.toColoring.valid h (x.2.injective he))

private theorem decode_partition {α : Type*} (P : G.Partition) (e : P.parts ↪ α) :
    (decode ⟨P, e⟩).toPartition = P := by
  have hparts : (decode ⟨P,e⟩).colorClasses = P.parts := by
    ext s
    constructor
    · rintro ⟨v, rfl⟩
      have hs : {w | decode ⟨P,e⟩ w = decode ⟨P,e⟩ v} = P.partOfVertex v := by
        ext w
        change e (P.toColoring w) = e (P.toColoring v) ↔ _
        rw [e.injective.eq_iff]
        constructor
        · intro he
          have hw := P.mem_partOfVertex w
          rwa [show P.partOfVertex w = P.partOfVertex v from congrArg Subtype.val he] at hw
        · intro hw
          exact part_eq P ⟨P.partOfVertex v, P.partOfVertex_mem v⟩ w hw
      change {w | decode ⟨P,e⟩ w = decode ⟨P,e⟩ v} ∈ P.parts
      rw [hs]
      exact P.partOfVertex_mem v
    · intro hs
      let t : P.parts := ⟨s,hs⟩
      refine ⟨representative P t, ?_⟩
      ext w
      change w ∈ s ↔ e (P.toColoring w) = e (P.toColoring (representative P t))
      rw [part_eq P t _ (representative_mem P t), e.injective.eq_iff]
      constructor
      · exact part_eq P t w
      · intro he
        have hw := P.mem_partOfVertex w
        rwa [show P.partOfVertex w = s from congrArg Subtype.val he] at hw
  cases P with
  | mk parts hp hi =>
    cases h : (decode ⟨⟨parts,hp,hi⟩,e⟩).toPartition with
    | mk parts' hp' hi' =>
      have : parts' = parts := by
        change (decode ⟨⟨parts,hp,hi⟩,e⟩).toPartition.parts = parts at hparts
        rw [h] at hparts
        exact hparts
      cases this
      rfl

private theorem decode_bijective {α : Type*} :
    Function.Bijective (@decode V G α) := by
  constructor
  · rintro ⟨P,e⟩ ⟨Q,d⟩ h
    have hp : P = Q := (decode_partition P e).symm.trans
      ((congrArg SimpleGraph.Coloring.toPartition h).trans (decode_partition Q d))
    cases hp
    have he : e = d := by
      apply Function.Embedding.ext
      intro s
      have hh := DFunLike.congr_fun h (representative P s)
      change e (P.toColoring (representative P s)) = d (P.toColoring (representative P s)) at hh
      simpa only [part_eq P s _ (representative_mem P s)] using hh
    cases he
    rfl
  · intro C
    let label : C.colorClasses → α := fun s => C (representative C.toPartition s)
    have mem_iff (s : C.colorClasses) (v : V) : v ∈ s.val ↔ C v = label s := by
      obtain ⟨w, hw⟩ := s.property
      have hr := representative_mem C.toPartition s
      change representative C.toPartition s ∈ s.val at hr
      rw [hw] at hr ⊢
      change C v = C w ↔ C v = C (representative C.toPartition s)
      rw [hr]
    let e : C.colorClasses ↪ α := ⟨label, by
      intro s t h
      apply Subtype.ext
      ext v
      rw [mem_iff, mem_iff, h]⟩
    refine ⟨⟨C.toPartition,e⟩, ?_⟩
    apply DFunLike.ext
    intro v
    exact ((mem_iff (C.toPartition.toColoring v) v).mp
      (C.toPartition.mem_partOfVertex v)).symm

/-- For every palette, including the empty palette, blocks carry distinct names.
The blocks are the actual Mathlib unlabelled nonempty independent vertex sets. -/
def coloringEquiv (G : SimpleGraph V) (α : Type*) :
    G.Coloring α ≃ Σ P : G.Partition, P.parts ↪ α :=
  (Equiv.ofBijective decode decode_bijective).symm

instance [Finite V] : Finite G.Partition :=
  Finite.of_injective (fun P : G.Partition => P.parts) (by
    rintro ⟨p,hp,hi⟩ ⟨q,hq,hj⟩ h
    cases h
    rfl)

instance [Finite V] : Fintype G.Partition := Fintype.ofFinite _

/-- The graphical Stirling number counts all partitions with exactly `j` blocks. -/
def stirling (G : SimpleGraph V) (j : ℕ) : ℕ :=
  Nat.card {P : G.Partition // Nat.card P.parts = j}

/-- The full finite falling-factorial expansion; no block or palette cap is imposed. -/
theorem chromatic_expansion [Fintype V] (G : SimpleGraph V) (q : ℕ) :
    Nat.card (G.Coloring (Fin q)) =
      ∑ j ∈ Finset.range (Fintype.card V + 1), q.descFactorial j * stirling G j := by
  classical
  have hbound (P : G.Partition) : Nat.card P.parts ≤ Fintype.card V := by
    have hs : Function.Surjective P.toColoring := by
      intro s
      exact ⟨representative P s, part_eq P s _ (representative_mem P s)⟩
    simpa using Nat.card_le_card_of_surjective P.toColoring hs
  have hc : Nat.card (G.Coloring (Fin q)) =
      ∑ P : G.Partition, q.descFactorial (Nat.card P.parts) := by
    rw [Nat.card_congr (coloringEquiv G (Fin q)), Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro P _
    letI := Fintype.ofFinite P.parts
    simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
  rw [hc]
  rw [← Finset.sum_fiberwise_of_maps_to' (f := fun j =>
    q.descFactorial j) (g := fun P : G.Partition => Nat.card P.parts)
    (t := Finset.range (Fintype.card V + 1)) (by
      intro P _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound P)))]
  apply Finset.sum_congr rfl
  intro j _
  simp [stirling, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_const, Nat.mul_comm]

end
end D5.S3.Combinatorics.Graph.Coloring.IndependentPartitionExpansion
