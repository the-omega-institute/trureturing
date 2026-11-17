/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Total and diagonal complexes and the Alexander-Whitney chain map. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# Alexander–Whitney and shuffle maps for bisimplicial objects

For a bisimplicial object `X` in an abelian category `C`, this file compares the total complex
`FOne(X)` of the double complex of alternating face maps with the alternating face map complex
`FTwo(X)` of the diagonal. It defines the Alexander–Whitney map `FTwo(X) ⟶ FOne(X)` and the
shuffle (Eilenberg–Zilber) map `FOne(X) ⟶ FTwo(X)`, proves that the shuffle map is a chain map via
the boundary formula for its components, and computes `alexanderWhitney ≫ shuffleMap`
degreewise (it is the identity in degree `0`). It also sets up the normalized complexes
`NOne(X)` and `NTwo(X)` together with their inclusions and retractions.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits

open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

variable {C : Type*} [Category* C]

variable (C) in
/-- A bisimplicial object in `C`: a simplicial object in simplicial objects in `C`. -/
abbrev BisimplicialObject := SimplicialObject (SimplicialObject C)

namespace BisimplicialObject

/-- The diagonal simplicial object `[n] ↦ X_{n,n}` of a bisimplicial object. -/
@[simps!]
def diag : BisimplicialObject C ⥤ SimplicialObject C :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj (Functor.diag _)

variable [Abelian C]

-- -- SimplicialObject is a `def` (not `abbrev`), so typeclass search doesn't
-- -- unfold it to `Functor SimplexCategoryᵒᵖ C` to find functorCategoryPreadditive.
-- instance : Preadditive (SimplicialObject C) := CategoryTheory.functorCategoryPreadditive


-- `SimplicialObject C` is a `def`, so the functor-category `Abelian` instance is not found by
-- unfolding; provide it explicitly (needed for the outer `normalizedMooreComplex`).
noncomputable instance : Abelian (SimplicialObject C) :=
  CategoryTheory.Abelian.functorCategoryAbelian

instance : (alternatingFaceMapComplex C).Additive := { }

open ComplexShape in
instance (K : ChainComplex (ChainComplex C ℕ) ℕ) :
    HomologicalComplex₂.HasTotal K (.down ℕ) := by
  intro n
  let f (pq : ((down ℕ).π (down ℕ) (down ℕ) ⁻¹' {n})) : Fin (n + 1) × Fin (n + 1) :=
    ⟨⟨pq.1.1, by
      have := pq.2
      simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at this
      lia⟩, ⟨pq.1.2, by
      have := pq.2
      simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at this
      lia⟩⟩
  have := Finite.of_injective f (fun _ _ ↦ by grind)
  infer_instance

/-- The total complex of the double complex obtained by taking alternating face map complexes in
both simplicial directions. -/
noncomputable abbrev FOne : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  alternatingFaceMapComplex _  ⋙
    (alternatingFaceMapComplex C).mapHomologicalComplex _ ⋙
      HomologicalComplex₂.totalFunctor _ _ _ _

/-- The alternating face map complex of the diagonal simplicial object. -/
abbrev FTwo : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  diag ⋙ alternatingFaceMapComplex C

/-- The double complex obtained by applying `alternatingFaceMapComplex` in both simplicial
directions. Its `(p, q)` entry is `X_{p,q}`. -/
noncomputable abbrev doubleComplex (X : BisimplicialObject C) :
    HomologicalComplex (ChainComplex C ℕ) (ComplexShape.down ℕ) :=
  ((alternatingFaceMapComplex C).mapHomologicalComplex _).obj
    ((alternatingFaceMapComplex (SimplicialObject C)).obj X)

/-! ### Basic simplicial maps

The Alexander-Whitney and shuffle maps are built from the standard front and back inclusions
`ιFront` and `ιBack`. -/

/-- Front face inclusion `[p] ⟶ [p+q]`: the unique monotone map sending `i ↦ i`. -/
def ιFront (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.1, by omega⟩, fun _ _ h => h⟩

/-- Back face inclusion `[q] ⟶ [p+q]`: the unique monotone map sending `j ↦ p + j`. -/
def ιBack (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨p + j.1, by omega⟩, fun _ _ h => Nat.add_le_add_left h _⟩

lemma val_eqToHom_apply {x y : SimplexCategory} (h : x = y) (i : Fin (x.len + 1)) :
    ((eqToHom h).toOrderHom i : ℕ) = i := by
  subst h
  rfl

/-- `ιFront(p, q) ≫ δ k = δ k ≫ ιFront(p+1, q)` when `k ≤ p`, i.e., the face map
acts within the front range. Here `δ k` on the left is `[p+q] → [p+q+1]` and
`δ k` on the right is `[p] → [p+1]`. -/
lemma ιFront_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2))
    (hk : (k : ℕ) ≤ p) :
    ιFront p q ≫ SimplexCategory.δ k =
      SimplexCategory.δ ⟨k, by omega⟩ ≫ ιFront (p + 1) q ≫
        eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  have hi' := hi
  simp only at hi'
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_eqToHom_apply]
  change (k.succAbove (⟨i, by omega⟩ : Fin (p + q + 1)) : ℕ) =
    ((⟨(k : ℕ), by omega⟩ : Fin (p + 2)).succAbove (⟨i, by omega⟩ : Fin (p + 1)) : ℕ)
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;>
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at * <;>
    omega

/-- `ιFront(p, q) ≫ δ k = ιFront(p, q+1)` when `k > p`, i.e., the face map
acts beyond the front range — all front vertices stay below the skipped index. -/
lemma ιFront_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2))
    (hk : p < (k : ℕ)) :
    ιFront p q ≫ SimplexCategory.δ k =
      ιFront p (q + 1) ≫ eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  have hi' := hi
  simp only at hi'
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_eqToHom_apply]
  change (k.succAbove (⟨i, by omega⟩ : Fin (p + q + 1)) : ℕ) = i
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;>
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at * <;>
    omega

/-- `ιBack(p, q) ≫ δ k = ιBack(p+1, q)` when `k ≤ p`, i.e., the face map
acts before the back range — all back vertices shift by one. -/
lemma ιBack_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2))
    (hk : (k : ℕ) ≤ p) :
    ιBack p q ≫ SimplexCategory.δ k =
      ιBack (p + 1) q ≫ eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  have hi' := hi
  simp only at hi'
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_eqToHom_apply]
  change (k.succAbove (⟨p + i, by omega⟩ : Fin (p + q + 1)) : ℕ) = p + 1 + i
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;>
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at * <;>
    omega

/-- `ιBack(p, q) ≫ δ k = δ (k - p) ≫ ιBack(p, q+1)` when `k > p`, i.e., the face
map acts within the back range. Here `δ (k-p)` is the face map on `[q]`. -/
lemma ιBack_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2))
    (hk : p < (k : ℕ)) :
    ιBack p q ≫ SimplexCategory.δ k =
      SimplexCategory.δ ⟨k - p, by omega⟩ ≫ ιBack p (q + 1) ≫
        eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  have hi' := hi
  simp only at hi'
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_eqToHom_apply]
  change (k.succAbove (⟨p + i, by omega⟩ : Fin (p + q + 1)) : ℕ) =
    p + ((⟨(k : ℕ) - p, by omega⟩ : Fin (q + 2)).succAbove
      (⟨i, by omega⟩ : Fin (q + 1)) : ℕ)
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;>
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at * <;>
    omega

/-- The top face of `[p+1]` followed by the front inclusion is the front inclusion
`[p] ⟶ [p+(q+1)]`, up to the arithmetic reassociation of the target. -/
private lemma δ_last_comp_ιFront (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ ιFront (p + 1) q =
      ιFront p (q + 1) ≫ eqToHom (by congr 1; omega) := by
  ext ⟨i, hi⟩
  have hi' := hi
  simp only at hi'
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_eqToHom_apply]
  change ((Fin.last (p + 1)).succAbove (⟨i, by omega⟩ : Fin (p + 1)) : ℕ) = i
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;>
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at * <;>
    omega

/-- The bottom face of `[q+1]` followed by the back inclusion shifts the back block
from offset `p` to offset `p+1`, up to the arithmetic reassociation of the target. -/
private lemma δ_zero_comp_ιBack (p q : ℕ) :
    SimplexCategory.δ 0 ≫ ιBack p (q + 1) =
      ιBack (p + 1) q ≫ eqToHom (by congr 1; omega) := by
  ext ⟨i, hi⟩
  have hi' := hi
  simp only at hi'
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_eqToHom_apply]
  change p + ((0 : Fin (q + 2)).succAbove (⟨i, by omega⟩ : Fin (q + 1)) : ℕ) =
    p + 1 + i
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;>
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at * <;>
    omega

/-! ### Alexander-Whitney map

The Alexander-Whitney map `FTwo(X) ⟶ FOne(X)` sends the diagonal chain complex to the total complex by
copairing the component maps `awComponent X p q` over all decompositions `p + q = n`. -/

/-- The `(p, q)` component of the Alexander-Whitney map. -/
noncomputable def awComponent (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) ⟶
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (X.map (ιFront p q).op).app (Opposite.op ⦋p + q⦌) ≫
    (X.obj (Opposite.op ⦋p⦌)).map (ιBack p q).op

omit [Abelian C] in
/-- Rewrite a diagonal face composed with an Alexander-Whitney component.

The result splits according to whether the face lands in the front block or the back block. -/
private lemma diag_δ_comp_eqToHom_awComponent (X : BisimplicialObject C)
    (n p q : ℕ) (hpq : p + q = n) (k : Fin (n + 2)) :
    (X.map (SimplexCategory.δ k).op).app (Opposite.op ⦋n + 1⦌) ≫
      (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.δ k).op ≫
        eqToHom (by subst hpq; rfl) ≫ awComponent X p q =
    if hk : (k : ℕ) ≤ p then
      eqToHom (by subst hpq; simp only [show p + 1 + q = p + q + 1 by omega]) ≫
        awComponent X (p + 1) q ≫
          (X.map (SimplexCategory.δ ⟨k, by omega⟩).op).app (Opposite.op ⦋q⦌)
    else
      eqToHom (by subst hpq; simp only [show p + (q + 1) = p + q + 1 by omega]) ≫
        awComponent X p (q + 1) ≫
          (X.obj (Opposite.op ⦋p⦌)).map
            (SimplexCategory.δ ⟨k - p, by omega⟩).op := by
  subst hpq
  unfold awComponent
  split_ifs with hk
  · simp only [Category.assoc]
    simp only [eqToHom_refl, Category.id_comp]
    slice_lhs 2 3 =>
      rw [(X.map (ιFront p q).op).naturality (SimplexCategory.δ k).op]
    simp only [Category.assoc]
    slice_lhs 1 2 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    rw [← op_comp, ιFront_comp_δ_of_le p q k hk]
    simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    slice_lhs 4 5 => rw [← Functor.map_comp, ← op_comp, ιBack_comp_δ_of_le p q k hk]
    simp only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map, eqToHom_app]
    generalize_proofs at *
    -- Apply θ = X.map (δ k).op naturality on the RHS w.r.t. the back-face ιBack, turning
    -- `X_⦋p+1⦌.map ιBack ≫ θ.app ⦋q⦌` into `θ.app ⦋p+1+q⦌ ≫ X_⦋p⦌.map ιBack`.
    slice_rhs 3 4 =>
      rw [(X.map (SimplexCategory.δ ⟨↑k, by omega⟩).op).naturality (ιBack (p + 1) q).op]
    -- Fuse the two vertical maps `η.app d ≫ θ.app d` into a single
    -- `(X.map (ιFront.op ≫ δ.op)).app d` on both sides, leaving one natural transformation.
    slice_lhs 2 3 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    slice_rhs 2 3 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    simp only [Category.assoc]
    -- Slide the leftover eqToHom (horizontal degree p+q+1 → p+1+q) across the fused map via
    -- its naturality for the cast morphism, lining both sides up at degree p+1+q. The goal has
    -- a bare `eqToHom`; first re-express it as `X_⦋p⦌.map (eqToHom _)` so naturality matches.
    slice_lhs 2 3 =>
      rw [← eqToHom_map (X _⦋p⦌) (show (Opposite.op ⦋p + q + 1⦌ : SimplexCategoryᵒᵖ) =
            Opposite.op ⦋p + 1 + q⦌ from by rw [show p + q + 1 = p + 1 + q from by omega])]
      rw [← (X.map ((ιFront (p + 1) q).op ≫ (SimplexCategory.δ ⟨↑k, by omega⟩).op)).naturality
        (eqToHom (show (Opposite.op ⦋p + q + 1⦌ : SimplexCategoryᵒᵖ) = Opposite.op ⦋p + 1 + q⦌ from
          by rw [show p + q + 1 = p + 1 + q from by omega]))]
    simp only [eqToHom_map, eqToHom_trans_assoc, Category.assoc]
  · simp only [Category.assoc]
    simp only [eqToHom_refl, Category.id_comp]
    slice_lhs 2 3 =>
      rw [(X.map (ιFront p q).op).naturality (SimplexCategory.δ k).op]
    simp only [Category.assoc]
    slice_lhs 1 2 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    rw [← op_comp, ιFront_comp_δ_of_gt p q k (by omega)]
    simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    slice_lhs 3 4 => rw [← Functor.map_comp, ← op_comp, ιBack_comp_δ_of_gt p q k (by omega)]
    simp only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map, eqToHom_app, Category.assoc]
    -- The two eqToHom casts collapse (`p+q+1` and `p+(q+1)` are defeq), leaving identical
    -- composites whose only difference is the defeq index `⦋p+q+1⦌` vs `⦋p+(q+1)⦌`.
    simp only [eqToHom_refl, Category.id_comp]
    rfl

omit [Abelian C] in
/-- `diag_δ_comp_eqToHom_awComponent`, stated with the diagonal face `(diag.obj X).map`. -/
private lemma diag_map_δ_comp_eqToHom_awComponent (X : BisimplicialObject C)
    (n p q : ℕ) (hpq : p + q = n) (k : Fin (n + 2)) :
    (diag.obj X).map (SimplexCategory.δ k).op ≫
        eqToHom (by subst hpq; rfl) ≫ awComponent X p q =
    if hk : (k : ℕ) ≤ p then
      eqToHom (by subst hpq; simp only [diag_obj_obj, show p + 1 + q = p + q + 1 by omega]) ≫
        awComponent X (p + 1) q ≫
          (X.map (SimplexCategory.δ ⟨k, by omega⟩).op).app (Opposite.op ⦋q⦌)
    else
      eqToHom (by subst hpq; simp only [diag_obj_obj, show p + (q + 1) = p + q + 1 by omega]) ≫
        awComponent X p (q + 1) ≫
          (X.obj (Opposite.op ⦋p⦌)).map
            (SimplexCategory.δ ⟨k - p, by omega⟩).op := by
  have h := diag_δ_comp_eqToHom_awComponent X n p q hpq k
  rw [← Category.assoc] at h
  exact h

omit [Abelian C] in
/-- The top face of `awComponent (p+1, q)` agrees with the bottom face of
`awComponent (p, q+1)`, up to the canonical arithmetic cast. -/
private lemma awComponent_top_face_eq_bottom_face (X : BisimplicialObject C) (p q : ℕ) :
    awComponent X (p + 1) q ≫
        (X.map (SimplexCategory.δ (Fin.last (p + 1))).op).app (Opposite.op ⦋q⦌) =
      eqToHom (by simp only [show p + 1 + q = p + (q + 1) by omega]) ≫
        awComponent X p (q + 1) ≫
        (X _⦋p⦌).map (SimplexCategory.δ 0).op := by
  unfold awComponent
  simp only [Category.assoc]
  rw [(X.map (SimplexCategory.δ (Fin.last (p + 1))).op).naturality
    (ιBack (p + 1) q).op]
  simp only [← Functor.map_comp]
  slice_lhs 1 2 => rw [← NatTrans.comp_app, ← Functor.map_comp]
  rw [← op_comp, δ_last_comp_ιFront]
  rw [← op_comp, δ_zero_comp_ιBack]
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  slice_lhs 1 1 => rw [eqToHom_op, eqToHom_map, eqToHom_app]
  slice_rhs 2 3 =>
    rw [← (X.map (ιFront p (q + 1)).op).naturality
      (eqToHom (by congr 1; omega)).op]
  simp only [Category.assoc, eqToHom_op, eqToHom_map, eqToHom_trans_assoc]

private lemma sum_bij_front {α : Type*} [AddCommMonoid α] {j : ℕ} (x : Fin (j + 1))
    {f : Fin (↑x + 1) → α}
    {g :
      {y : Fin (j + 2) // y ∈ Finset.univ.filter (fun y : Fin (j + 2) => (↑y : ℕ) ≤ ↑x)} → α}
    (hfg : ∀ i : Fin (↑x + 1),
      f i =
        g ⟨(⟨↑i, by omega⟩ : Fin (j + 2)), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega⟩) :
    ∑ i : Fin (↑x + 1), f i = ∑ y, g y := by
  refine Finset.sum_bij'
    (fun (i : Fin (↑x + 1)) _ => ⟨(⟨↑i, by omega⟩ : Fin (j + 2)), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩)
    (fun y _ => (⟨↑(↑y : Fin (j + 2)), by
      have := (Finset.mem_filter.mp y.2).2
      omega⟩ : Fin (↑x + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intros; rfl
  · intros; rfl
  · intros; simpa using hfg _

private lemma sum_bij_back {α : Type*} [AddCommMonoid α] {j : ℕ} (x : Fin (j + 1))
    {f : Fin (j - ↑x + 1) → α}
    {g :
      {y : Fin (j + 2) // y ∈ Finset.univ.filter (fun y : Fin (j + 2) => ¬ (↑y : ℕ) ≤ ↑x)} → α}
    (hfg : ∀ i : Fin (j - ↑x + 1),
      f i =
        g ⟨(⟨↑x + 1 + ↑i, by omega⟩ : Fin (j + 2)), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega⟩) :
    ∑ i : Fin (j - ↑x + 1), f i = ∑ y, g y := by
  refine Finset.sum_bij'
    (fun (i : Fin (j - ↑x + 1)) _ => ⟨(⟨↑x + 1 + ↑i, by omega⟩ : Fin (j + 2)), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩)
    (fun y _ => (⟨↑(↑y : Fin (j + 2)) - (↑x + 1), by
      have h1 := (Finset.mem_filter.mp y.2).2
      have h2 := (↑y : Fin (j + 2)).isLt
      omega⟩ : Fin (j - ↑x + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intros; apply Fin.ext; simp
  · intro y hy
    apply Subtype.ext; apply Fin.ext
    have hgt := (Finset.mem_filter.mp y.2).2
    simp at hgt ⊢
    omega
  · intros; simpa using hfg _

private lemma add_add_add_eq_of_eq {M : Type*} [AddCommMonoid M] {a b c d e f : M}
    (hae : a = e) (hdf : d = f) (hbc : b + c = 0) : a + b + (c + d) = e + f := by
  rw [← hae, ← hdf, add_assoc, ← add_assoc b, hbc, zero_add]

private lemma zsmul_add_zsmul_eq_zero {M : Type*} [AddCommGroup M] {s t : ℤ} {x y : M}
    (hst : s = -t) (hxy : x = y) : s • x + t • y = 0 := by
  rw [hst, hxy, neg_smul, neg_add_cancel]

/-- The Alexander-Whitney chain map `FTwo(X) ⟶ FOne(X)`. -/
noncomputable def alexanderWhitney (X : BisimplicialObject C) :
    FTwo.obj X ⟶ FOne.obj X where
  f n := by
    change (X.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) ⟶ _
    exact ∑ p : Fin (n + 1),
      eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫
        awComponent X p (n - p) ≫
          HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p (n - p) n (by
            simp only [ComplexShape.π_def, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)])
  comm' := by
    intro i j h
    simp only [id]
    rw [ComplexShape.down_Rel] at h;
    subst h
    -- Expand the total differential on the left into its `D₁ + D₂` pieces.
    change (∑ p : Fin (j + 2),
        eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)] :
          ((alternatingFaceMapComplex C).obj (diag.obj X)).X (j + 1) = _) ≫
        X.awComponent _ _ ≫
        HomologicalComplex₂.ιTotal X.doubleComplex (ComplexShape.down ℕ) _ _ (j + 1) _) ≫
      (HomologicalComplex₂.total X.doubleComplex (ComplexShape.down ℕ)).d (j + 1) j =
      ((alternatingFaceMapComplex C).obj (diag.obj X)).d (j + 1) j ≫
        ∑ p : Fin (j + 1),
          eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)] :
            (diag.obj X).obj (Opposite.op ⦋j⦌) = _) ≫
          X.awComponent _ _ ≫
          HomologicalComplex₂.ιTotal X.doubleComplex (ComplexShape.down ℕ) _ _ j _
    rw [Preadditive.sum_comp]
    simp only [Category.assoc]
    rw [HomologicalComplex₂.total_d]
    simp only [Preadditive.comp_add, Finset.sum_add_distrib,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    -- Expand the diagonal differential on the right as the alternating face sum.
    simp only [Preadditive.comp_sum]
    simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
      SimplicialObject.δ]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
    -- Rewrite each diagonal face through `awComponent`.
    -- `conv` is used here because the target term sits under nested sums and casts.
    conv_rhs =>
      enter [2, x, 2, x_1, 2]
      rw [reassoc_of% diag_map_δ_comp_eqToHom_awComponent X j (↑x) (j - ↑x)
        (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp x.isLt)) x_1]
    simp only [smul_dite, dite_comp]
    simp_rw [Finset.sum_dite]
    rw [Finset.sum_add_distrib]
    -- Separate off the two boundary faces so the remaining sums have matching index ranges.
    conv_lhs => rw [Fin.sum_univ_succ]
    rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), comp_zero, comp_zero, zero_add]
    conv_lhs => enter [2]; rw [Fin.sum_univ_castSucc]
    rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp), comp_zero, comp_zero, add_zero]
    -- Expand `d₁` and `d₂` into alternating face sums.
    conv_lhs =>
      enter [1, 2, i]
      rw [HomologicalComplex₂.d₁_eq _ _
            (show (ComplexShape.down ℕ).Rel (↑i.succ) ↑i by simp) _ _ (by simp; omega)]
    conv_lhs =>
      enter [2, 2, i]
      rw [HomologicalComplex₂.d₂_eq _ _ _
            (show (ComplexShape.down ℕ).Rel (j + 1 - ↑i.castSucc) (j - ↑i.castSucc) by
              simp; omega) _ (by simp; omega)]
    -- Replace the total-complex signs by their explicit formulas.
    simp_rw [show ∀ p q : ℕ,
              ((ComplexShape.down ℕ).ε₁ (.down ℕ) (.down ℕ) (p, q) : ℤˣ) = 1
              from fun _ _ => rfl,
             one_smul,
             show ∀ p q : ℕ,
              ((ComplexShape.down ℕ).ε₂ (.down ℕ) (.down ℕ) (p, q) : ℤˣ) = (-1 : ℤˣ)^p
              from fun _ _ => rfl]
    simp only [Fin.val_castSucc]
    -- Rewrite the `d₂` index into successor form before unfolding the differential.
    conv_lhs =>
      enter [2, 2, x]
      rw [(HomologicalComplex.eqToHom_comp_d _
            (show (ComplexShape.down ℕ).Rel (j + 1 - ↑x) (j - ↑x) by
              simp [ComplexShape.down_Rel]; omega)
            (show (ComplexShape.down ℕ).Rel ((j - ↑x) + 1) (j - ↑x) by
              simp [ComplexShape.down_Rel])).symm]
    conv_lhs =>
      enter [2, 2, x]
      simp only [Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X,
        alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, SimplicialObject.δ]
    -- Expose the `.f` component so `NatTrans.app` distributes over the sum.
    conv_lhs =>
      enter [1, 2, x]
      simp only [Fin.val_succ, doubleComplex, Functor.mapHomologicalComplex_obj_d,
        alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d,
        AlternatingFaceMapComplex.objD, SimplicialObject.δ]
    conv_lhs =>
      enter [1, 2, x]
      rw [NatTrans.app_sum, Finset.sum_congr rfl (fun x _ => NatTrans.app_zsmul _ _ _)]
    -- Distribute composition and scalar multiplication to put both sides into the same shape.
    simp only [Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
      Finset.smul_sum, smul_smul]
    -- Peel the remaining boundary faces so the interior ranges line up.
    conv_lhs =>
      enter [1, 2, x]
      rw [Fin.sum_univ_castSucc]
    conv_lhs =>
      enter [2, 2, x]
      rw [Fin.sum_univ_succ]
    simp only [Finset.sum_add_distrib]
    -- Match the interior sums after reindexing, and cancel the boundary pair.
    refine add_add_add_eq_of_eq ?_ ?_ ?_
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      refine sum_bij_front (x := x) ?_
      intro a
      have k : j + 1 - (↑x + 1) = j - ↑x := by omega
      generalize_proofs at *
      generalize j + 1 - (↑x + 1) = q at *
      subst k
      rfl
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      refine sum_bij_back
        (α := ((alternatingFaceMapComplex C).obj (diag.obj X)).X (j + 1) ⟶
          (HomologicalComplex₂.total X.doubleComplex (ComplexShape.down ℕ)).X j)
        (x := x) ?_
      intro a
      have k : j + 1 - ↑x = j - ↑x + 1 := by omega
      generalize_proofs at *
      generalize j + 1 - ↑x = q at *
      subst k
      simp only [eqToHom_refl, Category.id_comp]
      congr 1
      · push_cast
        rw [Fin.val_succ, pow_add]
        ring
      · congr
        apply Fin.ext
        simp
        omega
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro x _
      have k : j + 1 - (↑x + 1) = j - ↑x := by omega
      generalize_proofs at *
      generalize j + 1 - (↑x + 1) = q at *
      subst k
      simp only [Fin.val_zero, pow_zero, mul_one]
      refine zsmul_add_zsmul_eq_zero ?_ ?_
      · change ((-1 : ℤ) ^ ((Fin.last ((x.val : ℕ) + 1)).val : ℕ)) = -↑((-1 : ℤˣ) ^ x.val)
        rw [Fin.val_last, pow_succ, Units.val_pow_eq_pow_val]
        push_cast
        ring
      simp only [← Category.assoc]
      congr 1
      simp only [Category.assoc]
      rw [awComponent_top_face_eq_bottom_face]
      generalize hq : j + 1 - ↑x = q at *
      have hq' : j - ↑x + 1 = q := by omega
      subst hq'
      simp only [eqToHom_trans_assoc]
      congr 1
      simp only [eqToHom_refl, Category.id_comp]

end BisimplicialObject

end D5.S3.HomologicalAlgebra.EilenbergZilber
