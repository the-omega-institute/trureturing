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
import Mathlib.Order.Zorn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
import Mathlib.Tactic

/-! # Zero-one extreme points of finite matroid intersection rank regions -/


open scoped BigOperators
namespace D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope

variable {E : Type*} [DecidableEq E]

private structure TightChain (F : Finset E → Prop) where
  sets : Finset (Finset E)
  valid : ∀ A ∈ sets, F A
  chain : ∀ A ∈ sets, ∀ B ∈ sets, A ⊆ B ∨ B ⊆ A
  maximal : ∀ A, F A → (∀ B ∈ sets, A ⊆ B ∨ B ⊆ A) → A ∈ sets

omit [DecidableEq E] in
private lemma exists_tightChain [Finite E] (F : Finset E → Prop) :
    Nonempty (TightChain F) := by
  classical
  letI := Fintype.ofFinite E
  obtain ⟨S,hS,_⟩ :=
    (IsChain.empty : IsChain (· ≤ ·) (∅ : Set {A : Finset E // F A})).exists_maxChain
  let C := S.toFinset.image Subtype.val
  refine ⟨⟨C, ?_, ?_, ?_⟩⟩
  · intro A hA
    obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hA
    exact B.property
  · intro A hA B hB
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
    exact hS.isChain.total (by simpa using ha) (by simpa using hb)
  · intro A hA hcmp
    let a : {A : Finset E // F A} := ⟨A,hA⟩
    have hins : IsChain (· ≤ ·) (insert a S) := hS.isChain.insert (by
      intro b hb _
      exact hcmp b (Finset.mem_image.mpr ⟨b, by simpa using hb, rfl⟩))
    have ha : a ∈ S := by
      rw [hS.2 hins (Set.subset_insert _ _)]
      exact Set.mem_insert _ _
    exact Finset.mem_image.mpr ⟨a, by simpa using ha, rfl⟩

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
  rw [← Finset.sup_eq_biUnion]
  exact Finset.sup_induction h0 (fun A hA B hB => hu A B hA hB) hs

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


noncomputable def rankRegion [Finite E] (M1 M2 : Matroid E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
    ∀ U : Set E, (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((M1.eRk U).toNat : ℝ) ∧
      (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((M2.eRk U).toNat : ℝ)}

variable [Fintype E]

open Classical in
private lemma mem_rankRegion (M1 M2 : Matroid E) (x : E → ℝ) :
    x ∈ rankRegion M1 M2 ↔ (∀ e, 0 ≤ x e) ∧
      (∀ U : Set E, (∑ e ∈ U.toFinset, x e) ≤ ((M1.eRk U).toNat : ℝ)) ∧
      (∀ U : Set E, (∑ e ∈ U.toFinset, x e) ≤ ((M2.eRk U).toNat : ℝ)) := by
  simp [rankRegion, forall_and]

private def tight (M : Matroid E) (x : E → ℝ) (A : Finset E) : Prop :=
  (∑ e ∈ A, x e) = ((M.eRk (A : Set E)).toNat : ℝ)

omit [DecidableEq E] [Fintype E] in
private lemma tight_empty (M : Matroid E) (x : E → ℝ) : tight M x ∅ := by
  simp [tight]

open Classical in
private lemma tight_lattice (M : Matroid E) (x : E → ℝ)
    (hx : ∀ U : Set E, (∑ e ∈ U.toFinset, x e) ≤ ((M.eRk U).toNat : ℝ))
    {A B : Finset E} (hA : tight M x A) (hB : tight M x B) :
    tight M x (A ∪ B) ∧ tight M x (A ∩ B) := by
  classical
  have hsub := FiniteIntersection.rank_submod M (A : Set E) (B : Set E)
  have hsub' : ((M.eRk ((A ∩ B : Finset E) : Set E)).toNat : ℝ) +
      ((M.eRk ((A ∪ B : Finset E) : Set E)).toNat : ℝ) ≤
      ((M.eRk (A : Set E)).toNat : ℝ) + ((M.eRk (B : Set E)).toNat : ℝ) := by
    exact_mod_cast hsub
  have hsum := Finset.sum_union_inter (f := x) (s₁ := A) (s₂ := B)
  have hi := hx ((A ∩ B : Finset E) : Set E)
  have hu := hx ((A ∪ B : Finset E) : Set E)
  simp only [Finset.toFinset_coe] at hi hu
  unfold tight at *
  constructor <;> linarith

private noncomputable def subsetSum {E : Type u} [Fintype E] (U : Set E) :
    (E → ℝ) →ₗ[ℝ] ℝ := by
  classical
  exact { toFun := fun x => ∑ e ∈ U.toFinset, x e
          map_add' := by intros; simp [Finset.sum_add_distrib]
          map_smul' := by intros; simp [Finset.mul_sum] }

open Classical in
private theorem actual_active_kernel_zero {E : Type u} [Fintype E]
    (M1 M2 : Matroid E) (v : E → ℝ) (hv : v ∈ Set.extremePoints ℝ (rankRegion M1 M2))
    (d : E → ℝ)
    (h0 : ∀ e, v e = 0 → d e = 0)
    (h1 : ∀ U : Set E, (∑ e ∈ U.toFinset, v e) = ((M1.eRk U).toNat : ℝ) →
      (∑ e ∈ U.toFinset, d e) = 0)
    (h2 : ∀ U : Set E, (∑ e ∈ U.toFinset, v e) = ((M2.eRk U).toNat : ℝ) →
      (∑ e ∈ U.toFinset, d e) = 0) : d = 0 := by
  classical
  let a : E ⊕ (Set E ⊕ Set E) → (E → ℝ) →ₗ[ℝ] ℝ := fun j =>
    match j with
    | .inl e => -(LinearMap.proj e)
    | .inr (.inl U) => subsetSum U
    | .inr (.inr U) => subsetSum U
  let b : E ⊕ (Set E ⊕ Set E) → ℝ := fun j =>
    match j with
    | .inl _ => 0
    | .inr (.inl U) => ((M1.eRk U).toNat : ℝ)
    | .inr (.inr U) => ((M2.eRk U).toNat : ℝ)
  have hregion : rankRegion M1 M2 = {x : E → ℝ | ∀ j, a j x ≤ b j} := by
    ext x
    rw [mem_rankRegion]
    change ((∀ e, 0 ≤ x e) ∧
      (∀ U : Set E, (∑ e ∈ U.toFinset, x e) ≤ ((M1.eRk U).toNat : ℝ)) ∧
      (∀ U : Set E, (∑ e ∈ U.toFinset, x e) ≤ ((M2.eRk U).toNat : ℝ))) ↔ _
    constructor
    · rintro ⟨hx0, hx1, hx2⟩ j
      rcases j with e | (U | U)
      · simpa [a, b] using hx0 e
      · simpa [a, b, subsetSum] using hx1 U
      · simpa [a, b, subsetSum] using hx2 U
    · intro hx
      refine ⟨?_, ?_, ?_⟩
      · intro e
        simpa [a, b] using hx (.inl e)
      · intro U
        simpa [a, b, subsetSum] using hx (.inr (.inl U))
      · intro U
        simpa [a, b, subsetSum] using hx (.inr (.inr U))
  rw [hregion] at hv
  apply D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates.active_constraint_kernel_zero
    a b v hv d
  intro j hj
  rcases j with e | (U | U)
  · have hv0 : v e = 0 := by simpa [a, b] using hj
    simp [a, h0 e hv0]
  · have ht : (∑ e ∈ U.toFinset, v e) = ((M1.eRk U).toNat : ℝ) := by
      simpa [a, b, subsetSum] using hj
    simpa [a, subsetSum] using h1 U ht
  · have ht : (∑ e ∈ U.toFinset, v e) = ((M2.eRk U).toNat : ℝ) := by
      simpa [a, b, subsetSum] using hj
    simpa [a, subsetSum] using h2 U ht


private lemma compressed_kernel_zero (M1 M2 : Matroid E) (v : E → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (rankRegion M1 M2))
    (C : TightChain (tight M1 v)) (D : TightChain (tight M2 v)) (d : E → ℝ)
    (h0 : ∀ e, v e = 0 → d e = 0)
    (hC : ∀ A ∈ C.sets, (∑ e ∈ C.layer A, d e) = 0)
    (hD : ∀ A ∈ D.sets, (∑ e ∈ D.layer A, d e) = 0) : d = 0 := by
  classical
  have hfeas := (mem_rankRegion M1 M2 v).mp hv.1
  apply actual_active_kernel_zero M1 M2 v hv d h0
  · intro U hU
    have ht : tight M1 v U.toFinset := by simpa [tight] using hU
    exact C.kernel_compression (tight_empty M1 v)
      (fun A B hA hB => (tight_lattice M1 v hfeas.2.1 hA hB).1)
      (fun A B hA hB => (tight_lattice M1 v hfeas.2.1 hA hB).2) d hC ht
  · intro U hU
    have ht : tight M2 v U.toFinset := by simpa [tight] using hU
    exact D.kernel_compression (tight_empty M2 v)
      (fun A B hA hB => (tight_lattice M2 v hfeas.2.2 hA hB).1)
      (fun A B hA hB => (tight_lattice M2 v hfeas.2.2 hA hB).2) d hD ht

private noncomputable def layerRhs (M : Matroid E) (v : E → ℝ) (C : TightChain (tight M v))
    (A : C.sets) : ℤ := (M.eRk (A : Set E)).toNat -
      (M.eRk (C.pred A : Set E)).toNat

open Classical in
private lemma layer_consistent (M : Matroid E) (v : E → ℝ)
    (hv : ∀ U : Set E, (∑ e ∈ U.toFinset, v e) ≤ ((M.eRk U).toNat : ℝ))
    (C : TightChain (tight M v)) (A : C.sets) :
    (∑ e ∈ C.layer A, v e) = (layerRhs M v C A : ℝ) := by
  have hp := C.pred_valid (tight_empty M v)
    (fun A B hA hB => (tight_lattice M v hv hA hB).1) A
  rw [C.sum_layer]
  rw [C.valid A A.property, hp]
  simp [layerRhs]

private lemma layerMatrix_mulVec {F G : Finset E → Prop} (C : TightChain F) (D : TightChain G)
    (v : E → ℝ) :
    (layerMatrix C D).map (Int.castRingHom ℝ) *ᵥ v =
      Sum.elim (fun A : C.sets => ∑ e ∈ C.layer A, v e)
        (fun A : D.sets => -(∑ e ∈ D.layer A, v e)) := by
  classical
  ext r
  cases r <;> simp [Matrix.mulVec, dotProduct, layerMatrix]



private noncomputable def equationMatrix (v : E → ℝ)
    {F G : Finset E → Prop} (C : TightChain F) (D : TightChain G) :
    Matrix ((C.sets ⊕ D.sets) ⊕ {e : E // v e = 0}) E ℤ :=
  Matrix.fromRows (layerMatrix C D) (fun e j => if j = e then 1 else 0)

private lemma equationMatrix_zero_row (v : E → ℝ) {F G : Finset E → Prop}
    (C : TightChain F) (D : TightChain G) (e : {e : E // v e = 0}) (j : E) :
    equationMatrix v C D (.inr e) j = if j = e.val then 1 else 0 := by
  rfl

private noncomputable def equationRhs (M1 M2 : Matroid E) (v : E → ℝ)
    (C : TightChain (tight M1 v)) (D : TightChain (tight M2 v)) :
    (C.sets ⊕ D.sets) ⊕ {e : E // v e = 0} → ℤ :=
  Sum.elim (Sum.elim (layerRhs M1 v C) (fun A => -layerRhs M2 v D A)) (fun _ => 0)

omit [Fintype E] in
private lemma equationMatrix_tu (v : E → ℝ) {F G : Finset E → Prop}
    (C : TightChain F) (D : TightChain G) :
    (equationMatrix v C D).IsTotallyUnimodular := by
  classical
  apply (layerMatrix_tu C D).fromRows_unitlike
  intro _ e
  refine ⟨e, 1, ?_⟩
  ext j
  simp [Pi.single_apply]

private lemma equationMatrix_consistent (M1 M2 : Matroid E) (v : E → ℝ)
    (hv : v ∈ rankRegion M1 M2)
    (C : TightChain (tight M1 v)) (D : TightChain (tight M2 v)) :
    (equationMatrix v C D).map (Int.castRingHom ℝ) *ᵥ v =
      fun r => (equationRhs M1 M2 v C D r : ℝ) := by
  classical
  have hfeas := (mem_rankRegion M1 M2 v).mp hv
  ext r
  cases r with
  | inl r =>
    change ((layerMatrix C D).map (Int.castRingHom ℝ) *ᵥ v) r = _
    rw [layerMatrix_mulVec]
    cases r with
    | inl A => exact layer_consistent M1 v hfeas.2.1 C A
    | inr A => simpa [equationRhs] using congrArg Neg.neg (layer_consistent M2 v hfeas.2.2 D A)
  | inr e =>
    simpa [Matrix.mulVec, dotProduct, equationMatrix_zero_row, equationRhs,
      Sum.elim_inr] using e.property

private lemma equationMatrix_kernel (M1 M2 : Matroid E) (v : E → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (rankRegion M1 M2))
    (C : TightChain (tight M1 v)) (D : TightChain (tight M2 v))
    (d : E → ℝ)
    (hd : (equationMatrix v C D).map (Int.castRingHom ℝ) *ᵥ d = 0) : d = 0 := by
  classical
  apply compressed_kernel_zero M1 M2 v hv C D d
  · intro e he
    have h := congrFun hd (.inr ⟨e,he⟩)
    simpa [Matrix.mulVec, dotProduct, equationMatrix_zero_row] using h
  · intro A hA
    have h := congrFun hd (.inl (.inl ⟨A,hA⟩))
    change ((layerMatrix C D).map (Int.castRingHom ℝ) *ᵥ d) (.inl ⟨A,hA⟩) = 0 at h
    simpa only [layerMatrix_mulVec, Sum.elim_inl] using h
  · intro A hA
    have h := congrFun hd (.inl (.inr ⟨A,hA⟩))
    change ((layerMatrix C D).map (Int.castRingHom ℝ) *ᵥ d) (.inr ⟨A,hA⟩) = 0 at h
    simpa only [layerMatrix_mulVec, Sum.elim_inr, neg_eq_zero] using h

private lemma integer_solution_of_kernel_zero {R N : Type*} [Fintype R] [Fintype N]
    (A : Matrix R N ℤ) (hA : A.IsTotallyUnimodular) (b : R → ℤ) (v : N → ℝ)
    (hsol : A.map (Int.castRingHom ℝ) *ᵥ v = fun i => (b i : ℝ))
    (hker : ∀ d : N → ℝ, A.map (Int.castRingHom ℝ) *ᵥ d = 0 → d = 0) :
    ∃ z : N → ℤ, ∀ e, (z e : ℝ) = v e := by
  classical
  obtain ⟨B, hB⟩ :=
    D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse A hA
  let f := Int.castRingHom ℝ
  have hB' : A.map f * B.map f * A.map f = A.map f := by
    simpa only [Matrix.map_mul] using congrArg (fun T => T.map f) hB
  let z := B *ᵥ b
  have hzmap : (fun e => (z e : ℝ)) = B.map f *ᵥ (fun i => (b i : ℝ)) := by
    ext e
    exact f.map_mulVec B b e
  have hz : A.map f *ᵥ (fun e => (z e : ℝ)) = fun i => (b i : ℝ) := by
    rw [hzmap, ← hsol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB', hsol]
  have hd := hker ((fun e => (z e : ℝ)) - v) (by
    rw [Matrix.mulVec_sub, hz, hsol, sub_self])
  refine ⟨z, fun e => ?_⟩
  exact sub_eq_zero.mp (congrFun hd e)

omit [DecidableEq E] [Fintype E] in
theorem extreme_point_zero_one [Finite E] (M1 M2 : Matroid E)
    (_hM1 : M1.E = Set.univ) (_hM2 : M2.E = Set.univ)
    (v : E → ℝ) (hv : v ∈ Set.extremePoints ℝ
      {x : E → ℝ | (∀ e, 0 ≤ x e) ∧
        ∀ U : Set E, (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((M1.eRk U).toNat : ℝ) ∧
          (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((M2.eRk U).toNat : ℝ)}) :
    ∀ e, v e = 0 ∨ v e = 1 := by
  classical
  change v ∈ Set.extremePoints ℝ (rankRegion M1 M2) at hv
  letI := Fintype.ofFinite E
  have hfeas := (mem_rankRegion M1 M2 v).mp hv.1
  obtain ⟨C⟩ := exists_tightChain (tight M1 v)
  obtain ⟨D⟩ := exists_tightChain (tight M2 v)
  obtain ⟨z,hz⟩ := integer_solution_of_kernel_zero (equationMatrix v C D)
    (equationMatrix_tu v C D) (equationRhs M1 M2 v C D) v
    (equationMatrix_consistent M1 M2 v hv.1 C D)
    (equationMatrix_kernel M1 M2 v hv C D)
  intro e
  have hn : 0 ≤ v e := hfeas.1 e
  have hr : (M1.eRk {e}).toNat ≤ 1 := by
    rw [← ENat.natCast_le_natCast, FiniteIntersection.cast_toNat_eRk]
    exact M1.eRk_singleton_le e
  have he := hfeas.2.1 ({e} : Set E)
  simp only [Set.toFinset_singleton, Finset.sum_singleton] at he
  have hu : v e ≤ 1 := he.trans (by exact_mod_cast hr)
  have hz0 : (0 : ℤ) ≤ z e := by exact_mod_cast (hz e ▸ hn)
  have hz1 : z e ≤ (1 : ℤ) := by exact_mod_cast (hz e ▸ hu)
  have hcases : z e = 0 ∨ z e = 1 := by omega
  rcases hcases with he | he
  · left; rw [← hz e, he]; norm_num
  · right; rw [← hz e, he]; norm_num

#print axioms extreme_point_zero_one

end D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
