/- GID: D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech
   generality: G
   mirror-B: D5/B/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech
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
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
The horizontal direction is the supplied ordered free cover complex, with
coefficient object `R`, applied to each set of small singular simplices. The
vertical direction is obtained by the alternating-face-map functor. Thus its
differential is the actual singular boundary, and the two differentials
commute as morphisms in a category of chain complexes.

Only the augmentation is natural in the singular direction. No naturality of
the chosen vertex in the supplied row contraction is requested or used.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial BigOperators ZeroObject

universe w v u

namespace TauCeti.OrderedCechSingular

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C] (R : C)
  {ι : Type w} [LinearOrder ι]

lemma sum_chainMap_f {L M : ChainComplex C ℕ} {J : Type*} [Fintype J]
    (f : J → (L ⟶ M)) (n : ℕ) : (∑ j, f j).f n = ∑ j, (f j).f n :=
  map_sum (HomologicalComplex.Hom.fAddMonoidHom n) f Finset.univ

section SimplicialCover

variable (A : SSet.{w}) (P : ι → A.Subcomplex)

/-- The ordered row in every singular simplicial degree, including its actual maps. -/
def rows : SimplicialObject (ChainComplex C ℕ) where
  obj n := OrderedCover.complex R (fun i => (P i).obj n)
  map f := OrderedCover.map R (A.map f) (fun i a ha => (P i).map f ha)
  map_id n := by
    simpa only [A.map_id, CategoryTheory.types_id] using
      (OrderedCover.map_id R (P := fun i => (P i).obj n))
  map_comp f g := by
    simpa only [A.map_comp, CategoryTheory.types_comp] using
      (OrderedCover.map_comp R (A.map f) (A.map g)
        (fun i a ha => (P i).map f ha) (fun i a ha => (P i).map g ha))

/-- Outer degree is the ordered Cech degree; inner degree is singular degree. -/
def bicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip
    ((alternatingFaceMapComplex (ChainComplex C ℕ)).obj (rows R A P))

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
    erw [AlternatingFaceMapComplex.obj_d_eq, AlternatingFaceMapComplex.obj_d_eq]
    change _ ≫ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
      (sigmaConst.obj R).map (A.δ i)) = _
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, sum_chainMap_f,
      HomologicalComplex.zsmul_f_apply]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    symm
    apply OrderedCover.basis_hom_ext R
    intro s hs a ha
    simp [rows, SimplicialObject.δ, Category.assoc]

/-- The actual horizontal augmentation: sum the inclusions in Cech degree zero. -/
def horizontalAugmentation :
    bicomplex R A P ⟶ singleColumn (A.chainComplex R) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨horizontalColumnMap R A P, by
    ext q : 1
    have h := (OrderedCover.augmentation R
      (fun i => (P i).obj (op ⦋q⦌))).comm 1 0
    change (OrderedCover.complex R (fun i => (P i).obj (op ⦋q⦌))).d 1 0 ≫
      (OrderedCover.augmentation R (fun i => (P i).obj (op ⦋q⦌))).f 0 = 0
    simpa only [HomologicalComplex.single_obj_d,
      CategoryTheory.Limits.comp_zero] using h.symm⟩

/-- Evaluation transports a single column to the scalar single complex. -/
def singleColumnRowIso (L : ChainComplex C ℕ) (q : ℕ) :
    (singleColumn L).flip.X q ≅ (ChainComplex.single₀ C).obj (L.X q) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (HomologicalComplex.eval C (ComplexShape.down ℕ) q) (ComplexShape.down ℕ) 0).app L

/-- The row augmentation agrees after the canonical single-complex identification. -/
theorem horizontalAugmentation_flip_column (q : ℕ) :
    (((HomologicalComplex₂.flipFunctor C _ _).map
      (horizontalAugmentation R A P)).f q) ≫
        (singleColumnRowIso (A.chainComplex R) q).hom =
      OrderedCover.augmentation R (fun i => (P i).obj (op ⦋q⦌)) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [singleColumnRowIso, horizontalAugmentation, horizontalColumnMap,
    ChainComplex.single₀, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

/-- All row comparisons use the existing chosen-vertex contraction. -/
theorem horizontal_row_isIso
    (hP : ∀ n, ⋃ i, (P i).obj n = Set.univ) (q p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((HomologicalComplex₂.flipFunctor C _ _).map
        (horizontalAugmentation R A P)).f q) p) := by
  let f := (((HomologicalComplex₂.flipFunctor C _ _).map
    (horizontalAugmentation R A P)).f q)
  let e := singleColumnRowIso (A.chainComplex R) q
  have hcomp : IsIso (HomologicalComplex.homologyMap (f ≫ e.hom) p) := by
    dsimp only [f, e]
    rw [horizontalAugmentation_flip_column]
    obtain ⟨E, hE⟩ := OrderedCover.augmentation_homotopy_equiv R
      (fun i => (P i).obj (op ⦋q⦌)) (hP _)
    rw [← hE]
    change IsIso (E.toHomologyIso p).hom
    infer_instance
  have hcomp' : IsIso (HomologicalComplex.homologyMap f p ≫
      HomologicalComplex.homologyMap e.hom p) := by
    simpa only [HomologicalComplex.homologyMap_comp] using hcomp
  exact (isIso_comp_right_iff _ _).1 hcomp'

/-- The finite-degree comparison applies in the horizontal direction after flipping. -/
theorem horizontal_flipped_total_comparison
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
  (singleColumn L).totalDesc fun p q h =>
    if hp : p = 0 then by
      subst p
      exact (L.XIsoOfEq (by simpa using h)).hom
    else 0

private theorem singleColumnInclusion_isIso_f (n : ℕ) :
    IsIso ((singleColumnInclusion L).f n) := by
  refine ⟨singleColumnProjectionX L n, ?_, ?_⟩
  · simp only [singleColumnInclusion, singleColumnProjectionX, ι_totalDesc, dif_pos rfl,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    simp
  · apply total.hom_ext
    intro p q hpq
    cases p with
    | zero =>
      have hq : q = n := by simpa using hpq
      subst n
      simp only [singleColumnProjectionX, singleColumnInclusion, ι_totalDesc_assoc,
        dite_true, Nat.zero_add, HomologicalComplex.XIsoOfEq_rfl,
        Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (singleColumn L).XXIsoOfEq_hom_ιTotal (ComplexShape.down ℕ)
        (x₁ := 0) (y₁ := 0) rfl hq
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, q)) (by simp)
    | succ p =>
      have hz : IsZero (((singleColumn L).X (p + 1)).X q) := by
        exact (HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 L
            (p + 1) (by omega))
      exact hz.eq_of_src _ _

/-- Totalization of an actual single column, including all zero summands and signs. -/
def singleColumnTotalIso : (singleColumn L).total (ComplexShape.down ℕ) ≅ L := by
  haveI := singleColumnInclusion_isIso_f L
  haveI := HomologicalComplex.Hom.isIso_of_components (singleColumnInclusion L)
  exact (asIso (singleColumnInclusion L)).symm

private def singleRowFlipIso : (singleRow L).flip ≅ singleColumn L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => HomologicalComplex.Hom.isoOfComponents
      (fun p => if hq : q = 0 then by subst q; exact Iso.refl _
        else (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          (L.X p) q hq).iso
          ((HomologicalComplex.eval C (ComplexShape.down ℕ) p).map_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 L q hq)))
      (by
        intro p p' h
        by_cases hq : q = 0
        · subst q
          simp [singleRow, singleColumn, ChainComplex.single₀_map_f_zero]
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
            (L.X p) q hq).eq_of_src _ _))
    (by
      intro q q' h
      ext p : 1
      have hq : q ≠ 0 := by
        have : q' + 1 = q := h
        omega
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        (L.X p) q hq).eq_of_src _ _)

/-- Totalization of an actual single row via the signed native interchange. -/
def singleRowTotalIso : (singleRow L).total (ComplexShape.down ℕ) ≅ L :=
  ((singleRow L).totalFlipIso (ComplexShape.down ℕ)).symm ≪≫
    total.mapIso (singleRowFlipIso L) (ComplexShape.down ℕ) ≪≫ singleColumnTotalIso L

variable {L}

theorem horizontal_total_comparison
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
    rfl
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

variable {ι₀ : Type} [LinearOrder ι₀] (X : TopCat.{0}) (U : ι₀ → Set X)

/-- The actual simplicial set of subordinate singular simplices. -/
abbrev small : SSet.{0} := X.smallSingularSubcomplex U

/-- Subordinate simplices whose whole range is in one specified cover member. -/
def member (i : ι₀) : (small X U).Subcomplex where
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

theorem coefficientAugmentation_homology_zero :
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
    exact Category.comp_id _
  rw [← Category.assoc, ← Category.assoc, hσ]
  simp only [Category.assoc]
  rw [← Category.assoc (A.ιChainComplex σ) e.inv, hσ]
  rw [
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.liftCycles_i_assoc,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.comp_id,
    ι_coefficientAugmentation,
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε A R σ).symm

theorem isIso_coefficientAugmentation_of_contractible
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
