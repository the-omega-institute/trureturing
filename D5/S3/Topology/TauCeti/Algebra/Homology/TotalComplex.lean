/- GID: D5/S3/Topology/TauCeti/Algebra/Homology/TotalComplex
   generality: G
   mirror-B: D5/B/S3/Topology/TauCeti/Algebra/Homology/TotalComplex
   mirror-E: none(waiver:abstract-first-quadrant-comparison)
   anchors: []
   utility: none
   digest: Rowwise quasi-isomorphisms induce quasi-isomorphisms of native first-quadrant total complexes. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The extension-homology support retains the following source notice:
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
Adapted from https://github.com/TauCetiProject/TauCeti/pull/10141.

Selective adaptation of TauCetiProject/TauCeti revision
580580ea8726c50dcf98e199fa0a7caef5a74302, TotalComplex.lean (80–87, 243–586),
HomologySequenceLemmas.lean (73–126), and
Embedding/ExtendHomology/Basic.lean (64–82).
Modifications: receiving Mathlib imports and native extension/homology interfaces;
consumed support with selected public comparison interfaces;
augmentation, symmetry and singular-chain material omitted.
The full Apache-2.0 license is in docs/reports/licenses/tauceti-sphere-port-LICENSE.txt.
-/

import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.GradedObject.Monoidal
noncomputable section
open CategoryTheory Limits HomologicalComplex
universe v u
open CategoryTheory ComposableArrows Abelian
namespace HomologicalComplex.HomologySequence
variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
include hS₁ hS₂
private lemma mono_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : Mono (homologyMap φ.τ₁ j))
    (h₃ : Mono (homologyMap φ.τ₃ j)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)`.
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₁ i hij
    · exact h₂
    · exact h₃
  · have := hS₂.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    exact mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) this h₂ h₃

/-- The map `φ.τ₂` is surjective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are surjective in
degree `j` and `φ.τ₁` is injective in the degrees following `j`. -/
lemma epi_homologyMap_τ₂ (j : ι)
    (h₁ : Epi (homologyMap φ.τ₁ j))
    (h₂ : Epi (homologyMap φ.τ₃ j))
    (h₃ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    Epi (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    -- The exact sequence `H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)`.
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ j k hjk))
    · exact (composableArrows₅_exact hS₁ j k hjk).δlast.δlast
    · exact (composableArrows₅_exact hS₂ j k hjk).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ k hjk
  · have := hS₁.epi_g
    have := epi_homologyMap_of_epi_of_not_rel S₁.g j (by simpa using hj)
    exact epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₂ j) this h₁ h₂

/-- The map `φ.τ₂` is an isomorphism on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are
isomorphisms in degree `j`, `φ.τ₃` is surjective in the degrees preceding `j`, and `φ.τ₁` is
injective in the degrees following `j`. -/
lemma isIso_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : IsIso (homologyMap φ.τ₁ j))
    (h₃ : IsIso (homologyMap φ.τ₃ j))
    (h₄ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    IsIso (homologyMap φ.τ₂ j) := by
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ j h₁ inferInstance inferInstance
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ j inferInstance inferInstance h₄
  exact isIso_of_mono_of_epi _


end HomologicalComplex.HomologySequence
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex C c} (φ : K ⟶ L) {e : c.Embedding c'}
lemma epi_homologyMap_extendMap_iff {j : ι} {j' : ι'} (hj' : e.f j = j') :
    Epi (homologyMap (extendMap φ e) j') ↔ Epi (homologyMap φ j) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj') (by simp))
lemma isIso_homologyMap_extendMap_of_forall_ne {j' : ι'} (hj' : ∀ j, e.f j ≠ j') :
    IsIso (homologyMap (extendMap φ e) j') :=
  ⟨0, (K.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _,
    (L.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _⟩
end HomologicalComplex
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Preadditive C]
private instance hasTotal_down_nat [HasFiniteCoproducts C]
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := fun n ↦
  have : Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) :=
    inferInstanceAs (Finite ((fun i : ℕ × ℕ ↦ i.1 + i.2) ⁻¹' {n}))
  inferInstance

end HomologicalComplex₂
namespace ComplexShape
def embeddingDownNatSucc : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  embeddingDown'Add (1 : ℕ) 1
@[simp] private lemma embeddingDownNatSucc_f (n : ℕ) : embeddingDownNatSucc.f n = n + 1 := rfl
private instance : embeddingDownNatSucc.IsRelIff :=
  inferInstanceAs (embeddingDown'Add (1 : ℕ) 1).IsRelIff
end ComplexShape
namespace HomologicalComplex₂

open HomologicalComplex
open ComplexShape (embeddingDownNatSucc embeddingDownNatSucc_f)

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

omit [HasFiniteCoproducts C] in
/-- The rows `≥ 1` of `K`, reindexed so that row `q + 1` of `K` is row `q`. The summands are
`(K.X p).X (q + 1)` up to reducible unfolding, which lets rewriting identify them with those of
`K`. -/
private abbrev rowsSucc : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  X p :=
    { X q := (K.X p).X (q + 1)
      d q q' := (K.X p).d (q + 1) (q' + 1)
      shape q q' h := (K.X p).shape _ _ (by simp at h ⊢; omega) }
  d p p' := { f q := (K.d p p').f (q + 1) }
  shape p p' h := by ext q; exact HomologicalComplex.congr_hom (K.shape _ _ h) (q + 1)
  d_comp_d' p p' p'' _ _ := by
    ext q; exact HomologicalComplex.congr_hom (K.d_comp_d p p' p'') (q + 1)

/-- The inclusion of row `0` into the total complex. -/
noncomputable def rowZeroι :
    ((eval C (ComplexShape.down ℕ) 0).mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      K.total (ComplexShape.down ℕ) where
  f n := K.ιTotal (ComplexShape.down ℕ) n 0 n (by simp)
  comm' := by
    rintro _ n rfl
    rw [total_d, Preadditive.comp_add, ι_D₁, ι_D₂, d₂_eq_zero _ _ _ _ _ (by simp), add_zero,
      d₁_eq K _ (ComplexShape.down_mk _ _ rfl) 0 n (by simp)]
    simp

/-- The inclusion of row `0` sends the summand `(K.X n).X 0` into the total complex in degree
`n`. -/
@[simp]
lemma rowZeroι_f (n : ℕ) :
    (rowZeroι K).f n = K.ιTotal (ComplexShape.down ℕ) n 0 n (by simp) :=
  (rfl)

/-- The projection of the total complex in degree `n + 1` onto the total complex of `rowsSucc K`
in degree `n`, killing row `0`. -/
private noncomputable def dropRowZeroX (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X (n + 1) ⟶ ((rowsSucc K).total (ComplexShape.down ℕ)).X n :=
  K.totalDesc fun p q h ↦ match q, h with
    | 0, _ => 0
    | q + 1, h => (rowsSucc K).ιTotal (ComplexShape.down ℕ) p q n (by simp at h ⊢; omega)

@[reassoc (attr := simp)]
private lemma ιTotal_dropRowZeroX_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p 0 (n + 1) h ≫ dropRowZeroX K n = 0 := by
  simp [dropRowZeroX]

@[reassoc (attr := simp)]
private lemma ιTotal_dropRowZeroX_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p (q + 1) (n + 1) h ≫ dropRowZeroX K n =
      (rowsSucc K).ιTotal (ComplexShape.down ℕ) p q n (by simp at h ⊢; omega) := by
  simp only [dropRowZeroX, ι_totalDesc]

private lemma ιTotalOrZero_dropRowZeroX_succ (p q n : ℕ) :
    K.ιTotalOrZero (ComplexShape.down ℕ) p (q + 1) (n + 1) ≫ dropRowZeroX K n =
      (rowsSucc K).ιTotalOrZero (ComplexShape.down ℕ) p q n := by
  by_cases h : p + q = n
  · rw [K.ιTotalOrZero_eq _ _ _ _ (by simp; omega), ιTotal_dropRowZeroX_succ,
      ιTotalOrZero_eq _ _ _ _ _ (by simpa using h)]
  · rw [K.ιTotalOrZero_eq_zero _ _ _ _ (by simp; omega), zero_comp,
      ιTotalOrZero_eq_zero _ _ _ _ _ (by simpa using h)]

private lemma ιTotalOrZero_dropRowZeroX_zero (p n : ℕ) :
    K.ιTotalOrZero (ComplexShape.down ℕ) p 0 (n + 1) ≫ dropRowZeroX K n = 0 := by
  by_cases h : p = n + 1
  · rw [K.ιTotalOrZero_eq _ _ _ _ (by simpa using h), ιTotal_dropRowZeroX_zero]
  · rw [K.ιTotalOrZero_eq_zero _ _ _ _ (by simpa using h), zero_comp]

private lemma d₁_dropRowZeroX_succ (p q n : ℕ) :
    K.d₁ (ComplexShape.down ℕ) p (q + 1) (n + 1) ≫ dropRowZeroX K n =
      (rowsSucc K).d₁ (ComplexShape.down ℕ) p q n := by
  rcases p with _ | p
  · rw [d₁_eq_zero _ _ _ _ _ (by simp), d₁_eq_zero _ _ _ _ _ (by simp), zero_comp]
  · rw [d₁_eq' K _ (ComplexShape.down_mk _ _ rfl), d₁_eq' _ _ (ComplexShape.down_mk _ _ rfl),
      Linear.units_smul_comp, Category.assoc, ιTotalOrZero_dropRowZeroX_succ]
    -- Both signs `ε₁` are `1`, and the horizontal differentials of `rowsSucc K` are those of `K`
    -- by definition.
    rfl

private lemma d₁_dropRowZeroX_zero (p n : ℕ) :
    K.d₁ (ComplexShape.down ℕ) p 0 (n + 1) ≫ dropRowZeroX K n = 0 := by
  rcases p with _ | p
  · rw [d₁_eq_zero _ _ _ _ _ (by simp), zero_comp]
  · rw [d₁_eq' K _ (ComplexShape.down_mk _ _ rfl), Linear.units_smul_comp, Category.assoc,
      ιTotalOrZero_dropRowZeroX_zero, comp_zero, smul_zero]

private lemma d₂_dropRowZeroX_succ (p q n : ℕ) :
    K.d₂ (ComplexShape.down ℕ) p (q + 1) (n + 1) ≫ dropRowZeroX K n =
      (rowsSucc K).d₂ (ComplexShape.down ℕ) p q n := by
  rcases q with _ | q
  · rw [d₂_eq_zero (rowsSucc K) _ _ _ _ (by simp), d₂_eq' K _ _ (ComplexShape.down_mk _ _ rfl),
      Linear.units_smul_comp, Category.assoc, ιTotalOrZero_dropRowZeroX_zero, comp_zero,
      smul_zero]
  · rw [d₂_eq' K _ _ (ComplexShape.down_mk _ _ rfl), d₂_eq' _ _ _ (ComplexShape.down_mk _ _ rfl),
      Linear.units_smul_comp, Category.assoc, ιTotalOrZero_dropRowZeroX_succ]
    simp

/-- The projection killing row `0`, as a chain map out of the total complex restricted to the
degrees `≥ 1`. -/
private noncomputable def dropRowZeroAux :
    (K.total (ComplexShape.down ℕ)).restriction embeddingDownNatSucc ⟶
      (rowsSucc K).total (ComplexShape.down ℕ) where
  f n := dropRowZeroX K n
  comm' := by
    rintro _ n rfl
    refine total.hom_ext _ fun p q h ↦ ?_
    -- The differential of the restriction is that of the total complex in the shifted degrees.
    dsimp only [HomologicalComplex.restriction]
    simp only [embeddingDownNatSucc_f] at h ⊢
    rcases q with _ | q
    · simp only [ιTotal_dropRowZeroX_zero_assoc, zero_comp, total_d, Preadditive.add_comp,
        Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc, d₁_dropRowZeroX_zero,
        d₂_eq_zero _ _ _ _ _ (by simp : ¬ (ComplexShape.down ℕ).Rel 0 _), add_zero]
    · simp only [ιTotal_dropRowZeroX_succ_assoc, total_d, Preadditive.add_comp,
        Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc, ι_D₁, ι_D₂, d₁_dropRowZeroX_succ,
        d₂_dropRowZeroX_succ]

-- Every predecessor of a degree in the image of `embeddingDownNatSucc` is again in the image.
private lemma hasLift_dropRowZeroAux : embeddingDownNatSucc.HasLift (dropRowZeroAux K) :=
  fun j hj ↦ (hj.2 (j + 1) (ComplexShape.down_mk _ _ rfl)).elim

/-- The retraction of the total complex onto row `0` in degree `n`. -/
private noncomputable def rowZeroπX (n : ℕ) : (K.total (ComplexShape.down ℕ)).X n ⟶ (K.X n).X 0 :=
  K.totalDesc fun p q h ↦ match q, h with
    | 0, h => (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom
    | _ + 1, _ => 0

@[reassoc (attr := simp)]
private lemma ιTotal_rowZeroπX_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p 0 n h ≫ rowZeroπX K n =
      (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom := by
  simp [rowZeroπX]

@[reassoc (attr := simp)]
private lemma ιTotal_rowZeroπX_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p (q + 1) n h ≫ rowZeroπX K n = 0 := by
  simp [rowZeroπX]

/-- The section of `dropRowZeroX K n`. -/
private noncomputable def dropRowZeroSectionX (n : ℕ) :
    ((rowsSucc K).total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X (n + 1) :=
  (rowsSucc K).totalDesc fun p q h ↦ K.ιTotal (ComplexShape.down ℕ) p (q + 1) (n + 1)
    (by simp at h ⊢; omega)

@[reassoc (attr := simp)]
private lemma ιTotal_dropRowZeroSectionX (p q n : ℕ) (h) :
    (rowsSucc K).ιTotal (ComplexShape.down ℕ) p q n h ≫ dropRowZeroSectionX K n =
      K.ιTotal (ComplexShape.down ℕ) p (q + 1) (n + 1) (by simp at h ⊢; omega) := by
  simp [dropRowZeroSectionX]

@[reassoc (attr := simp)]
private lemma dropRowZeroSectionX_dropRowZeroX (n : ℕ) :
    dropRowZeroSectionX K n ≫ dropRowZeroX K n = 𝟙 _ := by
  ext p q h
  simp

section HasZeroObject

variable [HasZeroObject C]

/-- The projection of the total complex onto the total complex of the rows `≥ 1`, placed one
degree higher. -/
private noncomputable def dropRowZero :
    K.total (ComplexShape.down ℕ) ⟶
      ((rowsSucc K).total (ComplexShape.down ℕ)).extend embeddingDownNatSucc :=
  embeddingDownNatSucc.liftExtend (dropRowZeroAux K) (hasLift_dropRowZeroAux K)

private lemma dropRowZero_f_succ (n : ℕ) :
    (dropRowZero K).f (n + 1) =
      dropRowZeroX K n ≫ (((rowsSucc K).total (ComplexShape.down ℕ)).extendXIso embeddingDownNatSucc
        (embeddingDownNatSucc_f n)).inv := by
  rw [dropRowZero, embeddingDownNatSucc.liftExtend_f _ _ (embeddingDownNatSucc_f n)]
  -- The restriction isomorphism is an `eqToHom` between definitionally equal objects.
  exact Category.id_comp _

/-- The projection killing row `0` vanishes on the summands of row `0`. -/
@[simp]
private lemma rowZeroι_dropRowZero : rowZeroι K ≫ dropRowZero K = 0 := by
  ext (_ | n)
  · exact (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_tgt _ _
  · simp [dropRowZero_f_succ]

/-- The short complex `row 0 ⟶ Tot K ⟶ extend(Tot (rowsSucc K), n ↦ n + 1)`. It is an abbreviation so that its
objects are reducibly those of `K`. -/
private noncomputable abbrev rowZeroShortComplex :
    ShortComplex (HomologicalComplex C (ComplexShape.down ℕ)) :=
  ShortComplex.mk (rowZeroι K) (dropRowZero K) (rowZeroι_dropRowZero K)

/-- The short complex `rowZeroShortComplex K` in degree `n`, as a short complex in `C`. -/
private noncomputable abbrev rowZeroShortComplexX (n : ℕ) : ShortComplex C :=
  ShortComplex.mk ((rowZeroι K).f n) ((dropRowZero K).f n)
    (by rw [← HomologicalComplex.comp_f, rowZeroι_dropRowZero, HomologicalComplex.zero_f])

/-- The splitting of `rowZeroShortComplex K` in degree `n`: the retraction onto row `0` and, in
positive degrees, the inclusion of the rows `≥ 1`. -/
private noncomputable def rowZeroShortComplexXSplitting (n : ℕ) :
    (rowZeroShortComplexX K n).Splitting :=
  match n with
  | 0 =>
    { r := rowZeroπX K 0
      s := 0
      f_r := by simp
      s_g := (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_src _ _
      id := by
        refine total.hom_ext _ fun p q h ↦ ?_
        obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by simp at h; omega
        simp }
  | n + 1 =>
    { r := rowZeroπX K (n + 1)
      s := (((rowsSucc K).total (ComplexShape.down ℕ)).extendXIso embeddingDownNatSucc
        (embeddingDownNatSucc_f n)).hom ≫
        dropRowZeroSectionX K n
      f_r := by simp
      s_g := by simp [dropRowZero_f_succ]
      id := by
        refine total.hom_ext _ fun p q h ↦ ?_
        rcases q with _ | q
        · obtain rfl : p = n + 1 := by simpa using h
          simp [dropRowZero_f_succ]
        · simp [dropRowZero_f_succ] }

end HasZeroObject

variable {K} {L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (φ : K ⟶ L)

omit [HasFiniteCoproducts C] in
/-- The map of the bicomplexes of rows `≥ 1` induced by `φ`. -/
abbrev rowsSuccMap : rowsSucc K ⟶ rowsSucc L where
  f p := { f q := (φ.f p).f (q + 1) }

@[reassoc]
private lemma dropRowZeroX_naturality (n : ℕ) :
    dropRowZeroX K n ≫ (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)).f n =
      (total.map φ (ComplexShape.down ℕ)).f (n + 1) ≫ dropRowZeroX L n := by
  refine total.hom_ext _ fun p q h ↦ ?_
  rcases q with _ | q
  · simp
  · simp only [ιTotal_dropRowZeroX_succ_assoc, ιTotal_map, ιTotal_map_assoc,
      ιTotal_dropRowZeroX_succ]

variable [HasZeroObject C] in
/-- The map of short complexes induced by `φ`. -/
noncomputable def rowZeroShortComplexMap :
    rowZeroShortComplex K ⟶ rowZeroShortComplex L where
  τ₁ := ((eval C (ComplexShape.down ℕ) 0).mapHomologicalComplex _).map φ
  τ₂ := total.map φ (ComplexShape.down ℕ)
  τ₃ := extendMap (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)) embeddingDownNatSucc
  comm₁₂ := by
    ext n
    simp
  comm₂₃ := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    rcases n with _ | n
    · exact (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_tgt _ _
    · simp only [HomologicalComplex.comp_f, dropRowZero_f_succ,
        extendMap_f _ embeddingDownNatSucc (embeddingDownNatSucc_f n), Category.assoc,
        Iso.inv_hom_id_assoc]
      rw [dropRowZeroX_naturality_assoc]

end Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short complex `row 0 ⟶ Tot K ⟶ extend(Tot (rowsSucc K), n ↦ n + 1)` is short exact; it is split in each
degree. -/
lemma rowZeroShortComplex_shortExact
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    (rowZeroShortComplex K).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun n ↦ (rowZeroShortComplexXSplitting K n).shortExact

variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (φ : K ⟶ L)


open HomologySequence in
/-- If `φ` is a quasi-isomorphism on every row, then `Tot φ` is an isomorphism in homology below
`Q` and an epimorphism in degree `Q`. -/
private lemma total_map_aux (Q : ℕ) :
    ∀ {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (φ : K ⟶ L),
      (∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) →
        (∀ m < Q, IsIso (homologyMap (total.map φ (ComplexShape.down ℕ)) m)) ∧
          Epi (homologyMap (total.map φ (ComplexShape.down ℕ)) Q) := by
  induction Q with
  | zero =>
    intro K L φ hφ
    have : QuasiIso (rowZeroShortComplexMap φ).τ₁ := hφ 0
    refine ⟨fun m hm ↦ (Nat.not_lt_zero m hm).elim, ?_⟩
    exact epi_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
      (rowZeroShortComplex_shortExact L) 0 inferInstance
      ((extend_exactAt _ _ 0 fun _ ↦ by simp).isZero_homology.epi _) (fun k hk ↦ by simp at hk)
  | succ Q ih =>
    intro K L φ hφ
    have : QuasiIso (rowZeroShortComplexMap φ).τ₁ := hφ 0
    -- The rows of `rowsSucc K` are the rows `≥ 1` of `K`.
    obtain ⟨ih₁, ih₂⟩ := ih (rowsSuccMap φ) fun q ↦ hφ (q + 1)
    have hepi (m : ℕ) (hm : m ≤ Q) :
        Epi (homologyMap (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)) m) := by
      rcases hm.lt_or_eq with hm | rfl
      · have := ih₁ m hm
        infer_instance
      · exact ih₂
    refine ⟨fun m hm ↦ ?_, ?_⟩
    · refine isIso_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
        (rowZeroShortComplex_shortExact L) m ?_ inferInstance ?_ fun _ _ ↦ inferInstance
      · rintro i rfl
        exact (epi_homologyMap_extendMap_iff _ (embeddingDownNatSucc_f m)).2 (hepi m (by omega))
      · rcases m with _ | m
        · exact isIso_homologyMap_extendMap_of_forall_ne _ fun _ ↦ by simp
        · have := ih₁ m (by omega)
          rw [← quasiIsoAt_iff_isIso_homologyMap] at this ⊢
          exact (quasiIsoAt_extendMap_iff _ embeddingDownNatSucc (embeddingDownNatSucc_f m)).2 this
    · exact epi_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
        (rowZeroShortComplex_shortExact L) (Q + 1) inferInstance
        ((epi_homologyMap_extendMap_iff _ (embeddingDownNatSucc_f Q)).2 ih₂) fun _ _ ↦ inferInstance

/-- **A map of first-quadrant bicomplexes which is a quasi-isomorphism on every row induces a
quasi-isomorphism of total complexes.** Here the row `q` of a bicomplex `K` is the complex
`⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q` formed by the horizontal differentials. -/
theorem quasiIso_total_map_of_rows
    (hφ : ∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) :
    QuasiIso (total.map φ (ComplexShape.down ℕ)) := by
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (total_map_aux (m + 1) φ hφ).1 m (Nat.lt_succ_self m)


end HomologicalComplex₂
