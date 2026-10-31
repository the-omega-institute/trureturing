/- GID: D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/FiniteIntersectionPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extreme points of two finite matroid rank-inequality regions have zero-one coordinates. -/

import D5.S3.Combinatorics.Matroids.FiniteIntersection
import D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
import D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
import Mathlib.Tactic

open scoped BigOperators
namespace D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
variable {E : Type*} [DecidableEq E]

private structure TightChain (F : Finset E → Prop) where
  sets : Finset (Finset E)
  valid : ∀ A ∈ sets, F A
  chain : ∀ A ∈ sets, ∀ B ∈ sets, A ⊆ B ∨ B ⊆ A
  maximal : ∀ A, F A → (∀ B ∈ sets, A ⊆ B ∨ B ⊆ A) → A ∈ sets

private lemma exists_tightChain [Fintype E] (F : Finset E → Prop) : Nonempty (TightChain F) := by
  classical
  let good : Finset (Finset (Finset E)) := Finset.univ.filter fun C =>
    (∀ A ∈ C, F A) ∧ (∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A)
  have hgood : (∅ : Finset (Finset E)) ∈ good := by simp [good]
  obtain ⟨C, hC, hmax⟩ := good.exists_max_image Finset.card ⟨∅, hgood⟩
  have hC' := (Finset.mem_filter.mp hC).2
  refine ⟨⟨C, hC'.1, hC'.2, ?_⟩⟩
  intro A hA hcmp
  by_contra hn
  have hins : insert A C ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hA
      · exact hC'.1 B hB
    · intro B hB D hD
      rcases Finset.mem_insert.mp hB with hBA | hBC
      · subst B
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact Or.inl (Finset.Subset.refl _)
        · exact hcmp D hD
      · rcases Finset.mem_insert.mp hD with hDA | hDC
        · subst D
          exact (hcmp B hBC).symm
        · exact hC'.2 B hBC D hDC
  have := hmax _ hins
  simp [Finset.card_insert_of_notMem hn] at this

namespace TightChain
variable {F : Finset E → Prop} (C : TightChain F)

private def pred (A : Finset E) : Finset E :=
  (C.sets.filter fun B => B ⊂ A).biUnion id

private def layer (A : Finset E) : Finset E := A \ C.pred A

private lemma pred_subset (A : Finset E) : C.pred A ⊆ A := by
  intro e he
  obtain ⟨B, hB, he⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_filter.mp hB).2.1 he

private lemma subset_pred {A B : Finset E} (hB : B ∈ C.sets) (hBA : B ⊂ A) : B ⊆ C.pred A := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hB, hBA⟩, he⟩

private lemma union_valid (h0 : F ∅) (hu : ∀ A B, F A → F B → F (A ∪ B))
    (s : Finset (Finset E)) (hs : ∀ A ∈ s, F A) : F (s.biUnion id) := by
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert A s hn ih =>
    simp only [Finset.biUnion_insert]
    exact hu _ _ (hs A (by simp)) (ih fun B hB => hs B (by simp [hB]))

private lemma pred_valid (h0 : F ∅) (hu : ∀ A B, F A → F B → F (A ∪ B))
    (A : Finset E) : F (C.pred A) := by
  exact union_valid h0 hu _ fun B hB => C.valid B (Finset.mem_filter.mp hB).1

private lemma tight_subset_top (h0 : F ∅) (hu : ∀ A B, F A → F B → F (A ∪ B))
    {U : Finset E} (hU : F U) : U ⊆ C.sets.biUnion id := by
  let T := C.sets.biUnion id
  have ht : F T := union_valid h0 hu _ C.valid
  have hm : T ∪ U ∈ C.sets := C.maximal _ (hu _ _ ht hU) (by
    intro B hB
    right
    exact fun e he => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨B,hB,he⟩))
  intro e he
  exact Finset.mem_biUnion.mpr ⟨T ∪ U,hm,Finset.mem_union_right _ he⟩

private lemma layer_saturated (h0 : F ∅) (hu : ∀ A B, F A → F B → F (A ∪ B))
    (hi : ∀ A B, F A → F B → F (A ∩ B))
    {A U : Finset E} (hA : A ∈ C.sets) (hU : F U) :
    C.layer A ⊆ U ∨ Disjoint (C.layer A) U := by
  let D := C.pred A ∪ (U ∩ A)
  have hD : F D := hu _ _ (C.pred_valid h0 hu A) (hi _ _ hU (C.valid A hA))
  have hDA : D ⊆ A := Finset.union_subset (C.pred_subset A) Finset.inter_subset_right
  have hm : D ∈ C.sets := C.maximal _ hD (by
    intro B hB
    rcases C.chain B hB A hA with hBA | hAB
    · by_cases heq : B = A
      · subst B; exact Or.inl hDA
      · right
        exact (C.subset_pred hB (Finset.ssubset_iff_subset_ne.mpr ⟨hBA,heq⟩)).trans Finset.subset_union_left
    · exact Or.inl (hDA.trans hAB))
  by_cases heq : D = A
  · left
    intro e he
    have heA := (Finset.mem_sdiff.mp he).1
    have heD : e ∈ D := heq.symm ▸ heA
    rcases Finset.mem_union.mp heD with hep | heu
    · exact False.elim ((Finset.mem_sdiff.mp he).2 hep)
    · exact (Finset.mem_inter.mp heu).1
  · right
    apply Finset.disjoint_left.mpr
    intro e he heu
    have hep : e ∈ C.pred A := C.subset_pred hm
      (Finset.ssubset_iff_subset_ne.mpr ⟨hDA,heq⟩)
      (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨heu,(Finset.mem_sdiff.mp he).1⟩))
    exact (Finset.mem_sdiff.mp he).2 hep

private lemma layers_disjoint {A B : Finset E} (hA : A ∈ C.sets) (hB : B ∈ C.sets)
    (hne : A ≠ B) : Disjoint (C.layer A) (C.layer B) := by
  rcases C.chain A hA B hB with hAB | hBA
  · apply Finset.disjoint_left.mpr
    intro e heA heB
    exact (Finset.mem_sdiff.mp heB).2 (C.subset_pred hA
      (Finset.ssubset_iff_subset_ne.mpr ⟨hAB,hne⟩) (Finset.mem_sdiff.mp heA).1)
  · apply Finset.disjoint_left.mpr
    intro e heA heB
    exact (Finset.mem_sdiff.mp heA).2 (C.subset_pred hB
      (Finset.ssubset_iff_subset_ne.mpr ⟨hBA,hne.symm⟩) (Finset.mem_sdiff.mp heB).1)

private lemma mem_some_layer {e : E} (he : e ∈ C.sets.biUnion id) :
    ∃ A ∈ C.sets, e ∈ C.layer A := by
  classical
  let S := C.sets.filter fun A => e ∈ A
  have hn : S.Nonempty := by
    obtain ⟨A,hA,heA⟩ := Finset.mem_biUnion.mp he
    exact ⟨A,Finset.mem_filter.mpr ⟨hA,heA⟩⟩
  obtain ⟨A,hA,hmin⟩ := S.exists_min_image Finset.card hn
  obtain ⟨hAC,heA⟩ := Finset.mem_filter.mp hA
  refine ⟨A,hAC,Finset.mem_sdiff.mpr ⟨heA,?_⟩⟩
  intro hep
  obtain ⟨B,hB,heB⟩ := Finset.mem_biUnion.mp hep
  obtain ⟨hBC,hBA⟩ := Finset.mem_filter.mp hB
  have hle := hmin B (Finset.mem_filter.mpr ⟨hBC,heB⟩)
  have hlt := Finset.card_lt_card hBA
  omega

private lemma sum_eq_layers (h0 : F ∅) (hu : ∀ A B, F A → F B → F (A ∪ B))
    {U : Finset E} (hU : F U) (d : E → ℝ) :
    (∑ e ∈ U, d e) = ∑ A ∈ C.sets, ∑ e ∈ C.layer A ∩ U, d e := by
  have hdecomp : U = C.sets.biUnion (fun A => C.layer A ∩ U) := by
    ext e
    constructor
    · intro he
      obtain ⟨A,hA,heA⟩ := C.mem_some_layer (C.tight_subset_top h0 hu hU he)
      exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_inter.mpr ⟨heA,he⟩⟩
    · intro he
      obtain ⟨A,_,heA⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_inter.mp heA).2
  conv_lhs => rw [hdecomp]
  apply Finset.sum_biUnion
  intro A hA B hB hne
  exact (C.layers_disjoint hA hB hne).mono Finset.inter_subset_left Finset.inter_subset_left

private lemma kernel_compression (h0 : F ∅) (hu : ∀ A B, F A → F B → F (A ∪ B))
    (hi : ∀ A B, F A → F B → F (A ∩ B)) (d : E → ℝ)
    (hd : ∀ A ∈ C.sets, (∑ e ∈ C.layer A, d e) = 0)
    {U : Finset E} (hU : F U) : (∑ e ∈ U, d e) = 0 := by
  rw [C.sum_eq_layers h0 hu hU d]
  apply Finset.sum_eq_zero
  intro A hA
  rcases C.layer_saturated h0 hu hi hA hU with hsub | hdisj
  · rw [Finset.inter_eq_left.mpr hsub]
    exact hd A hA
  · simp [Finset.disjoint_iff_inter_eq_empty.mp hdisj]

private lemma sum_layer (A : Finset E) (d : E → ℝ) :
    (∑ e ∈ C.layer A, d e) = (∑ e ∈ A, d e) - ∑ e ∈ C.pred A, d e := by
  exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff (C.pred_subset A) (f := d))

private noncomputable def owner (e : E) : Option C.sets :=
  if h : ∃ A : C.sets, e ∈ C.layer A then some (Classical.choose h) else none

private lemma owner_eq_iff (A : C.sets) (e : E) : C.owner e = some A ↔ e ∈ C.layer A := by
  classical
  unfold owner
  split_ifs with h
  · constructor
    · intro heq
      have heq' := Option.some.inj heq
      exact heq' ▸ Classical.choose_spec h
    · intro he
      congr 1
      by_contra hne
      have hd := C.layers_disjoint (Classical.choose h).property A.property
        (fun hh => hne (Subtype.ext hh))
      exact Finset.disjoint_left.mp hd (Classical.choose_spec h) he
  · constructor
    · intro he; cases he
    · intro he; exact False.elim (h ⟨A,he⟩)

end TightChain
open Matrix
open D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity

private noncomputable def layerMatrix {F G : Finset E → Prop} (C : TightChain F) (D : TightChain G) :
    Matrix (C.sets ⊕ D.sets) E ℤ :=
  fun r e => match r with
    | .inl A => if e ∈ C.layer A then 1 else 0
    | .inr A => -(if e ∈ D.layer A then 1 else 0)

private lemma layerMatrix_tu {F G : Finset E → Prop} (C : TightChain F) (D : TightChain G) :
    (layerMatrix C D).IsTotallyUnimodular := by
  classical
  let tail : E → Option C.sets ⊕ Option D.sets := fun e => .inr (D.owner e)
  let head : E → Option C.sets ⊕ Option D.sets := fun e => .inl (C.owner e)
  let row : C.sets ⊕ D.sets → Option C.sets ⊕ Option D.sets :=
    Sum.elim (fun A => .inl (some A)) (fun A => .inr (some A))
  have ht := (signed_incidence_is_totally_unimodular tail head).submatrix row id
  convert ht using 1
  ext r e
  cases r with
  | inl A =>
    simp only [layerMatrix, Matrix.submatrix_apply, signedIncidence, row, tail, head,
      Sum.elim_inl, id_eq, Sum.inl.injEq, reduceCtorEq, ite_false, sub_zero]
    simp only [eq_comm (a := some A), C.owner_eq_iff]
  | inr A =>
    simp only [layerMatrix, Matrix.submatrix_apply, signedIncidence, row, tail, head,
      Sum.elim_inr, id_eq, Sum.inr.injEq, reduceCtorEq, ite_false, zero_sub]
    simp only [eq_comm (a := some A), D.owner_eq_iff]

end D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
