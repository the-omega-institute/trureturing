/- GID: D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech
   generality: G
   mirror-B: none(waiver:source-artifact-awaiting-canonical-validation)
   mirror-E: none(waiver:abstract-chain-construction)
   anchors: []
   utility: none
   digest: The actual ordered Cech and singular bicomplex and horizontal augmentation. -/

/-
The signed-interchange naturality calculation and the single-column inclusion
adapt the proof patterns in the Tau Ceti support files
`Algebra/Homology/FiniteDegreeComparison.lean` and `TotalComplex.lean`, at
trureturing revision 22ce62dbe632fd8d2dae1caf58967e87c531b5b7.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see
docs/reports/licenses/tauceti-sphere-port-LICENSE.txt in the receiving repository.
-/

import D5.S3.Topology.TauCeti.Algebra.Homology.OrderedCechCover
import D5.S3.Topology.TauCeti.Algebra.Homology.FiniteDegreeComparison
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Contractible
import Mathlib.Algebra.Homology.SingleHomology

/-!
The horizontal direction is the supplied ordered free cover complex, with
coefficient object `R`, applied to each set of small singular simplices. The
vertical direction is obtained by the alternating-face-map functor. Thus its
differential is the actual singular boundary, and the two differentials
commute as morphisms in a category of chain complexes.

Only the augmentation is natural in the singular direction. No naturality of
the chosen vertex in the supplied row contraction is requested or used.

This source artifact has not been elaborated or compiled.
-/

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial BigOperators

universe w v u

namespace TauCeti.OrderedCechSingular

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCoproducts.{w} C] (R : C)
  {ι : Type w} [LinearOrder ι]

lemma sum_chainMap_f {L M : ChainComplex C ℕ} {J : Type*} [Fintype J]
    (f : J → (L ⟶ M)) (n : ℕ) : (∑ j, f j).f n = ∑ j, (f j).f n :=
  (HomologicalComplex.Hom.fAddMonoidHom n).map_sum f Finset.univ

section SimplicialCover

variable (A : SSet.{w}) (P : ι → A.Subcomplex)

/-- The ordered row in every singular simplicial degree, including its actual maps. -/
def rows : SimplicialObject (ChainComplex C ℕ) where
  obj n := OrderedCover.complex R (fun i => (P i).obj n)
  map f := OrderedCover.map R (A.map f) (fun i a ha => (P i).map f ha)
  map_id n := by
    simpa only [A.map_id] using
      (OrderedCover.map_id R (P := fun i => (P i).obj n))
  map_comp f g := by
    simpa only [A.map_comp, TypeCat.comp_apply] using
      (OrderedCover.map_comp R (A.map f) (A.map g)
        (fun i a ha => (P i).map f ha) (fun i a ha => (P i).map g ha))

/-- Outer degree is the ordered Cech degree; inner degree is singular degree. -/
def bicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ((alternatingFaceMapComplex (ChainComplex C ℕ)).obj (rows R A P)).flip

/-- Each row is literally the supplied ordered-cover chain complex. -/
theorem flip_column (q : ℕ) :
    (bicomplex R A P).flip.X q = OrderedCover.complex R (fun i => (P i).obj (op ⦋q⦌)) :=
  rfl

/-- The two actual differentials commute before totalization. -/
theorem horizontal_vertical_commute (p p' q q' : ℕ) :
    ((bicomplex R A P).d p p').f q ≫ ((bicomplex R A P).X p').d q q' =
      ((bicomplex R A P).X p).d q q' ≫ ((bicomplex R A P).d p p').f q' :=
  (bicomplex R A P).d_comm p p' q q'

/-- A zero column away from Cech degree zero. -/
abbrev singleColumn (L : ChainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (ChainComplex.single₀ (ChainComplex C ℕ)).obj L

private def horizontalColumnMap : (bicomplex R A P).X 0 ⟶ A.chainComplex R where
  f q := (OrderedCover.augmentation R (fun i => (P i).obj (op ⦋q⦌))).f 0
  comm' := by
    rintro _ q rfl
    change (OrderedCover.augmentation R (fun i => (P i).obj (op ⦋q + 1⦌))).f 0 ≫
      (A.chainComplex R).d (q + 1) q =
      (((alternatingFaceMapComplex (ChainComplex C ℕ)).obj (rows R A P)).d
        (q + 1) q).f 0 ≫
        (OrderedCover.augmentation R (fun i => (P i).obj (op ⦋q⦌))).f 0
    rw [AlternatingFaceMapComplex.obj_d_eq]
    change _ ≫ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
      (sigmaConst.obj R).map (A.δ i)) = _
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, sum_chainMap_f,
      HomologicalComplex.zsmul_f_apply]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    symm
    exact (HomologicalComplex.congr_hom
      (OrderedCover.map_augmentation R (A.δ i)
        (fun j a ha => (P j).map (SimplexCategory.δ i).op ha)) 0)

/-- The actual horizontal augmentation: sum the inclusions in Cech degree zero. -/
def horizontalAugmentation :
    bicomplex R A P ⟶ singleColumn (A.chainComplex R) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨horizontalColumnMap R A P, by
    ext q : 1
    have h := (OrderedCover.augmentation R
      (fun i => (P i).obj (op ⦋q⦌))).comm 1 0
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.single_obj_d,
      CategoryTheory.Limits.comp_zero] using h.symm⟩

/-- On a horizontal row this is exactly the supplied augmentation, with `R` unchanged. -/
theorem horizontalAugmentation_flip_column (q : ℕ) :
    (((HomologicalComplex₂.flipFunctor C _ _).map
      (horizontalAugmentation R A P)).f q) =
      OrderedCover.augmentation R (fun i => (P i).obj (op ⦋q⦌)) := by
  apply HomologicalComplex.to_single_hom_ext
  rfl

/-- All row comparisons use the existing chosen-vertex contraction. -/
theorem horizontal_row_isIso [CategoryWithHomology C]
    (hP : ∀ n, ⋃ i, (P i).obj n = Set.univ) (q p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((HomologicalComplex₂.flipFunctor C _ _).map
        (horizontalAugmentation R A P)).f q) p) := by
  rw [horizontalAugmentation_flip_column]
  obtain ⟨E, hE⟩ := OrderedCover.augmentation_homotopy_equiv R
    (fun i => (P i).obj (op ⦋q⦌)) (hP _)
  rw [← hE]
  change IsIso (E.toHomologyIso p).hom
  infer_instance

/-- The finite-degree comparison applies in the horizontal direction after flipping. -/
theorem horizontal_flipped_total_comparison [Abelian C]
    (hP : ∀ n, ⋃ i, (P i).obj n = Set.univ) :
    (∀ n ≤ 1, IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor C _ _).map
          (horizontalAugmentation R A P)) (ComplexShape.down ℕ)) n)) ∧
      Epi (HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map
          ((HomologicalComplex₂.flipFunctor C _ _).map
            (horizontalAugmentation R A P)) (ComplexShape.down ℕ)) 2) := by
  apply HomologicalComplex₂.finite_degree_comparison_total_map 1
  · intro q p hpq
    exact horizontal_row_isIso R A P hP q p
  · intro q p hpq
    have := horizontal_row_isIso R A P hP q p
    infer_instance

end SimplicialCover

section TotalIdentifications

open HomologicalComplex₂

variable (L : ChainComplex C ℕ)

/-- An ordinary complex placed in singular degree zero. -/
abbrev singleRow : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ((ChainComplex.single₀ C).mapHomologicalComplex (ComplexShape.down ℕ)).obj L

private def singleColumnInclusion : L ⟶ (singleColumn L).total (ComplexShape.down ℕ) where
  f n := (singleColumn L).ιTotal (ComplexShape.down ℕ) 0 n n (by simp)
  comm' := by
    rintro _ n rfl
    rw [total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
      (singleColumn L).d₁_eq_zero (ComplexShape.down ℕ) 0 (n + 1) n (by simp), zero_add,
      (singleColumn L).d₂_eq (ComplexShape.down ℕ) 0
        (ComplexShape.down_mk _ _ rfl) n (by simp)]
    simp

private def singleColumnProjectionX (n : ℕ) :
    ((singleColumn L).total (ComplexShape.down ℕ)).X n ⟶ L.X n :=
  (singleColumn L).totalDesc fun p q h => match p, h with
    | 0, h => (L.XIsoOfEq (by simpa using h)).hom
    | _ + 1, _ => 0

private theorem singleColumnInclusion_isIso_f (n : ℕ) :
    IsIso ((singleColumnInclusion L).f n) := by
  refine ⟨singleColumnProjectionX L n, ?_, ?_⟩
  · simp only [singleColumnInclusion, singleColumnProjectionX, ι_totalDesc,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  · apply total.hom_ext
    intro p q hpq
    cases p with
    | zero =>
      have hq : q = n := by simpa using hpq
      subst n
      simp only [singleColumnProjectionX, ι_totalDesc, Category.assoc,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
        singleColumnInclusion, Category.comp_id]
    | succ p =>
      have hz : IsZero (((singleColumn L).X (p + 1)).X q) := by
        change IsZero (0 : C)
        exact isZero_zero C
      exact hz.eq_of_src _ _

/-- Totalization of an actual single column, including all zero summands and signs. -/
def singleColumnTotalIso : (singleColumn L).total (ComplexShape.down ℕ) ≅ L := by
  haveI := singleColumnInclusion_isIso_f L
  haveI := HomologicalComplex.isIso_of_components (singleColumnInclusion L)
  exact (asIso (singleColumnInclusion L)).symm

private def singleRowFlipIso : (singleRow L).flip ≅ singleColumn L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => HomologicalComplex.Hom.isoOfComponents
      (fun p => by cases q <;> exact Iso.refl _)
      (by
        intro p p' h
        cases q <;> simp [singleRow, singleColumn, ChainComplex.single₀_map_f_zero]))
    (by
      intro q q' h
      ext p : 1
      cases q <;> cases q' <;> simp [singleRow, singleColumn])

/-- Totalization of an actual single row via the signed native interchange. -/
def singleRowTotalIso : (singleRow L).total (ComplexShape.down ℕ) ≅ L :=
  ((singleRow L).totalFlipIso (ComplexShape.down ℕ)).symm ≪≫
    total.mapIso (singleRowFlipIso L) (ComplexShape.down ℕ) ≪≫ singleColumnTotalIso L

variable {L}

theorem horizontal_total_comparison [Abelian C]
    (A : SSet.{w}) (P : ι → A.Subcomplex)
    (hP : ∀ n, ⋃ i, (P i).obj n = Set.univ) :
    (∀ n ≤ 1, IsIso (HomologicalComplex.homologyMap
      (total.map (horizontalAugmentation R A P) (ComplexShape.down ℕ)) n)) ∧
      Epi (HomologicalComplex.homologyMap
        (total.map (horizontalAugmentation R A P) (ComplexShape.down ℕ)) 2) := by
  let D := bicomplex R A P
  let E := singleColumn (A.chainComplex R)
  let φ : D ⟶ E := horizontalAugmentation R A P
  let ψ : D.flip ⟶ E.flip := (flipFunctor C _ _).map φ
  obtain ⟨hI, hE⟩ := horizontal_flipped_total_comparison R A P hP
  have hnat : total.map ψ (ComplexShape.down ℕ) ≫
      (E.totalFlipIso (ComplexShape.down ℕ)).hom =
      (D.totalFlipIso (ComplexShape.down ℕ)).hom ≫ total.map φ (ComplexShape.down ℕ) := by
    ext n q p h
    dsimp only [HomologicalComplex.comp_f]
    simp only [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom,
      ιTotal_totalFlipIso_f_hom_assoc, Linear.units_smul_comp, Linear.comp_units_smul,
      ιTotal_map, flipFunctor_map_f_f]
  have hmap : total.map φ (ComplexShape.down ℕ) =
      (D.totalFlipIso (ComplexShape.down ℕ)).inv ≫ total.map ψ (ComplexShape.down ℕ) ≫
        (E.totalFlipIso (ComplexShape.down ℕ)).hom := by
    rw [hnat, Iso.inv_hom_id_assoc]
  change (∀ n ≤ 1, IsIso (HomologicalComplex.homologyMap
    (total.map φ (ComplexShape.down ℕ)) n)) ∧ _
  constructor
  · intro n hn
    haveI := hI n hn
    rw [hmap]
    simp only [HomologicalComplex.homologyMap_comp]
    infer_instance
  · haveI := hE
    rw [hmap]
    simp only [HomologicalComplex.homologyMap_comp]
    infer_instance

end TotalIdentifications

section ActualCover

variable (X : TopCat.{w}) (U : ι → Set X)

/-- The actual simplicial set of subordinate singular simplices. -/
abbrev small : SSet.{w} := X.smallSingularSubcomplex U

/-- Subordinate simplices whose whole range is in one specified cover member. -/
def member (i : ι) : (small X U).Subcomplex where
  obj n := {σ | Set.range (X.toSSetObjEquiv n σ.val) ⊆ U i}
  map f σ := by
    intro hσ
    rintro _ ⟨z, rfl⟩
    exact hσ ⟨_, (TopCat.toSSetObjEquiv_naturality_apply f.unop σ.val z).symm⟩

theorem members_cover (n : SimplexCategoryᵒᵖ) :
    ⋃ i, (member X U i).obj n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro σ
  exact Set.mem_iUnion.mpr σ.property

/-- Cech--singular chains made from the given real cover, with integer coefficients. -/
abbrev integerBicomplex :=
  bicomplex (ModuleCat.of ℤ ℤ) (small X U) (member X U)

/-- Its honest horizontal augmentation to small singular chains in column zero. -/
abbrev integerHorizontalAugmentation :=
  horizontalAugmentation (ModuleCat.of ℤ ℤ) (small X U) (member X U)

end ActualCover

section CoefficientAugmentation

variable (A : SSet.{w})

/-- The ordinary sum of coefficients of singular zero-chains. -/
def sumCoefficients : (A.chainComplex R).X 0 ⟶ R :=
  Sigma.desc fun _ => 𝟙 R

@[reassoc (attr := simp)]
theorem ι_sumCoefficients (σ : A _⦋0⦌) :
    A.ιChainComplex σ ≫ sumCoefficients R A = 𝟙 R :=
  Sigma.ι_comp_desc _ _

theorem d_sumCoefficients :
    (A.chainComplex R).d 1 0 ≫ sumCoefficients R A = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ι_sumCoefficients]
  simp [Fin.sum_univ_two]

/-- Zero in positive degree; coefficient sum in degree zero. -/
def coefficientAugmentation :
    A.chainComplex R ⟶ (ChainComplex.single₀ C).obj R :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨sumCoefficients R A, d_sumCoefficients R A⟩

@[reassoc (attr := simp)]
theorem ι_coefficientAugmentation (σ : A _⦋0⦌) :
    A.ιChainComplex σ ≫ (coefficientAugmentation R A).f 0 = 𝟙 R := by
  rw [coefficientAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  exact ι_sumCoefficients R A σ

theorem coefficientAugmentation_homology_zero [CategoryWithHomology C] :
    HomologicalComplex.homologyMap (coefficientAugmentation R A) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 R).hom =
        A.homology₀ε R := by
  let c := A.chainComplex R
  let e : c.cycles 0 ≅ c.X 0 := c.iCyclesIso 0 0 (by simp) (by simp)
  apply (cancel_epi (c.homologyπ 0)).1
  apply (cancel_epi e.inv).1
  apply SSet.chainComplex_hom_ext
  intro σ
  have hσ : A.ιChainComplex σ ≫ e.inv =
      c.liftCycles (A.ιChainComplex σ) 0 (by simp) (by simp) := by
    apply (cancel_mono (c.iCycles 0)).1
    simp [e, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hσ]
  rw [Category.assoc, Category.assoc,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.liftCycles_i_assoc,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.comp_id,
    ι_coefficientAugmentation,
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]

theorem isIso_coefficientAugmentation_of_contractible [CategoryWithHomology C]
    (X : TopCat.{w}) [ContractibleSpace X] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (coefficientAugmentation R (TopCat.toSSet.obj X)) n) := by
  cases n with
  | zero =>
    have h := coefficientAugmentation_homology_zero R (TopCat.toSSet.obj X)
    haveI : IsIso ((TopCat.toSSet.obj X).homology₀ε R) := inferInstance
    haveI : IsIso (HomologicalComplex.homologyMap
        (coefficientAugmentation R (TopCat.toSSet.obj X)) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 R).hom) := by
      rw [h]
      infer_instance
    exact (isIso_comp_right_iff
      (HomologicalComplex.homologyMap
        (coefficientAugmentation R (TopCat.toSSet.obj X)) 0)
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 R).hom).1
        inferInstance
  | succ n =>
    have hX := TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace R X
      n.succ_ne_zero
    have hR := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.down ℕ) 0 R (n + 1) n.succ_ne_zero
    exact ⟨0, hX.eq_of_src _ _, hR.eq_of_src _ _⟩

end CoefficientAugmentation

end TauCeti.OrderedCechSingular
