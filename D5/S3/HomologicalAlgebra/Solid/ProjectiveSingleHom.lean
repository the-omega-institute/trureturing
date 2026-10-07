/- GID: D5/S3/HomologicalAlgebra/Solid/ProjectiveSingleHom
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ProjectiveSingleHom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive Limits HomologicalComplex
namespace CWSolid
set_option backward.isDefEq.respectTransparency false

section ProjectiveSingle

variable {C : Type*} [Category* C] [Abelian C]

/-- The canonical homology class of a map from a single complex. -/
def singleHomologyMap (A : C) (n : ℤ) (K : CochainComplex C ℤ)
    (f : (CochainComplex.singleFunctor C n).obj A ⟶ K) : A ⟶ K.homology n :=
  (singleObjHomologySelfIso (.up ℤ) n A).inv ≫ homologyMap f n

lemma singleHomologyMap_eq (A : C) (n : ℤ) (K : CochainComplex C ℤ)
    (f : (CochainComplex.singleFunctor C n).obj A ⟶ K) :
    singleHomologyMap A n K f =
      (singleObjCyclesSelfIso (.up ℤ) n A).inv ≫ cyclesMap f n ≫ K.homologyπ n := by
  simp [singleHomologyMap, ← homologyπ_naturality,
    ← singleObjCyclesSelfIso_inv_homologyπ_assoc,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors]

lemma singleHomologyMap_surjective (A : C) [Projective A] (n : ℤ)
    (K : CochainComplex C ℤ) : Function.Surjective (singleHomologyMap A n K) := by
  intro h
  let z := Projective.factorThru h (K.homologyπ n)
  let f : (CochainComplex.singleFunctor C n).obj A ⟶ K :=
    mkHomFromSingle (z ≫ K.iCycles n) (by
      intro k hk
      simp only [Category.assoc, K.iCycles_d, comp_zero])
  refine ⟨f, ?_⟩
  have hz : (singleObjCyclesSelfIso (.up ℤ) n A).inv ≫ cyclesMap f n = z := by
    apply (cancel_mono (K.iCycles n)).1
    simp [f, cyclesMap_i, mkHomFromSingle_f, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  rw [singleHomologyMap_eq, ← Category.assoc, hz]
  exact Projective.factorThru_comp h (K.homologyπ n)

lemma singleHomologyMap_zero_nullhomotopic (A : C) [Projective A] (n : ℤ)
    (K : CochainComplex C ℤ)
    (f : (CochainComplex.singleFunctor C n).obj A ⟶ K)
    (hf : singleHomologyMap A n K f = 0) : Nonempty (Homotopy f 0) := by
  let z := (singleObjCyclesSelfIso (.up ℤ) n A).inv ≫ cyclesMap f n
  have hz : z ≫ K.homologyπ n = 0 := by
    simpa only [z, Category.assoc, ← singleHomologyMap_eq] using hf
  let S := ShortComplex.mk (K.toCycles (n - 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n - 1) n)
  have hS : S.Exact :=
    S.exact_of_g_is_cokernel (K.homologyIsCokernel (n - 1) n (by simp))
  let b : A ⟶ K.X (n - 1) := hS.liftFromProjective z hz
  have hb : b ≫ K.d (n - 1) n = (singleObjXSelf (.up ℤ) n A).inv ≫ f.f n := by
    rw [← K.toCycles_i (n - 1) n, ← Category.assoc,
      show b ≫ K.toCycles (n - 1) n = z from hS.liftFromProjective_comp z hz]
    simp [z, cyclesMap_i, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  let h : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel j i →
      (((CochainComplex.singleFunctor C n).obj A).X i ⟶ K.X j) := fun i j hij =>
    if hi : i = n then
      (singleObjXIsoOfEq (.up ℤ) n A i hi).hom ≫ b ≫
        (K.XIsoOfEq (show n - 1 = j by have hij' : j + 1 = i := hij; omega)).hom
    else 0
  have hh : Homotopy.nullHomotopicMap' h = f := by
    apply from_single_hom_ext
    rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (n - 1) n by
      change n - 1 + 1 = n; omega) (show (ComplexShape.up ℤ).Rel n (n + 1) by rfl)]
    simp only [single_obj_d, zero_comp, zero_add]
    dsimp [h]
    simp only [dite_true, comp_id, Category.assoc]
    change (singleObjXSelf (.up ℤ) n A).hom ≫ b ≫ K.d (n - 1) n = f.f n
    rw [hb]
    simp
  exact ⟨hh ▸ Homotopy.nullHomotopy' h⟩

variable [HasDerivedCategory C]

/-- Canonical normalization of the homology of a derived single object. -/
def derivedSingleHomologyIso (A : C) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.singleFunctor C n).obj A) ≅ A :=
  (DerivedCategory.homologyFunctorFactors C n).app
    ((CochainComplex.singleFunctor C n).obj A) ≪≫
      singleObjHomologySelfIso (.up ℤ) n A

/-- Apply homology to a derived morphism, with the canonical single-source normalization. -/
def derivedSingleHomologyMap (A : C) (n : ℤ) (Y : DerivedCategory C)
    (f : (DerivedCategory.singleFunctor C n).obj A ⟶ Y) :
    A ⟶ (DerivedCategory.homologyFunctor C n).obj Y :=
  (derivedSingleHomologyIso A n).inv ≫ (DerivedCategory.homologyFunctor C n).map f

@[reassoc]
lemma derivedSingleHomologyMap_naturality (A : C) (n : ℤ)
    {Y Z : DerivedCategory C} (f : (DerivedCategory.singleFunctor C n).obj A ⟶ Y)
    (g : Y ⟶ Z) :
    derivedSingleHomologyMap A n Z (f ≫ g) =
      derivedSingleHomologyMap A n Y f ≫ (DerivedCategory.homologyFunctor C n).map g := by
  simp [derivedSingleHomologyMap]

lemma derivedSingleHomologyMap_Q_map (A : C) (n : ℤ) (K : CochainComplex C ℤ)
    (f : (CochainComplex.singleFunctor C n).obj A ⟶ K) :
    derivedSingleHomologyMap A n (DerivedCategory.Q.obj K) (DerivedCategory.Q.map f) =
      singleHomologyMap A n K f ≫ (DerivedCategory.homologyFunctorFactors C n).inv.app K := by
  simp only [derivedSingleHomologyMap, derivedSingleHomologyIso, singleHomologyMap,
    Iso.trans_inv, Iso.app_inv, Category.assoc]
  simpa only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] using
    congrArg (fun u => (singleObjHomologySelfIso (.up ℤ) n A).inv ≫ u)
      ((DerivedCategory.homologyFunctorFactors C n).inv.naturality f).symm

/-- Localization is surjective on maps from this single projective source only. -/
lemma Q_map_surjective_projective_single (A : C) [Projective A] (n : ℤ)
    (K : CochainComplex C ℤ) :
    Function.Surjective (DerivedCategory.Q.map :
      ((CochainComplex.singleFunctor C n).obj A ⟶ K) → _) := by
  let S := (CochainComplex.singleFunctor C n).obj A
  haveI (i : ℤ) : Projective (S.X i) := by
    change Projective (((single C (.up ℤ) n).obj A).X i)
    infer_instance
  have : S.IsKProjective := CochainComplex.isKProjective_of_projective S n
  let eS := (DerivedCategory.quotientCompQhIso C).app S
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective S
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)).surjective (eS.hom ≫ f ≫ eK.inv)
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  refine ⟨g', ?_⟩
  have h := congrArg (fun u => u ≫ eK.hom) hg
  apply (cancel_epi eS.hom).1
  simpa [eS, eK, DerivedCategory.quotientCompQhIso_hom_naturality] using h

lemma derivedSingleHomologyMap_Q_bijective (A : C) [Projective A] (n : ℤ)
    (K : CochainComplex C ℤ) :
    Function.Bijective (derivedSingleHomologyMap A n (DerivedCategory.Q.obj K)) := by
  constructor
  · intro f g hfg
    have hz : derivedSingleHomologyMap A n (DerivedCategory.Q.obj K) (f - g) = 0 := by
      change (derivedSingleHomologyIso A n).inv ≫
        (DerivedCategory.homologyFunctor C n).map (f - g) = 0
      rw [Functor.map_sub, comp_sub]
      exact sub_eq_zero.mpr hfg
    obtain ⟨u, hu⟩ := (Q_map_surjective_projective_single A n K) (f - g)
    have hu' : singleHomologyMap A n K u = 0 := by
      rw [← hu, derivedSingleHomologyMap_Q_map] at hz
      exact (cancel_mono ((DerivedCategory.homologyFunctorFactors C n).inv.app K)).1
        (by simpa using hz)
    obtain ⟨h⟩ := singleHomologyMap_zero_nullhomotopic A n K u hu'
    have h0 := DerivedCategory.Q_map_eq_of_homotopy C h
    rw [hu, Functor.map_zero] at h0
    exact sub_eq_zero.mp h0
  · intro h
    obtain ⟨u, hu⟩ := singleHomologyMap_surjective A n K
      (h ≫ (DerivedCategory.homologyFunctorFactors C n).hom.app K)
    refine ⟨DerivedCategory.Q.map u, ?_⟩
    simp [derivedSingleHomologyMap_Q_map, hu, Category.assoc]

/-- Every target in the unbounded derived category is allowed. No replacement hypothesis. -/
theorem derivedSingleHomologyMap_bijective (A : C) [Projective A] (n : ℤ)
    (Y : DerivedCategory C) : Function.Bijective (derivedSingleHomologyMap A n Y) := by
  let K := DerivedCategory.Q.objPreimage Y
  let e : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  constructor
  · intro f g hfg
    have h := (derivedSingleHomologyMap_Q_bijective A n K).injective
      (show derivedSingleHomologyMap A n _ (f ≫ e.inv) =
        derivedSingleHomologyMap A n _ (g ≫ e.inv) by
        simp only [derivedSingleHomologyMap_naturality, hfg])
    exact (cancel_mono e.inv).1 h
  · intro h
    obtain ⟨f, hf⟩ := (derivedSingleHomologyMap_Q_bijective A n K).surjective
      (h ≫ (DerivedCategory.homologyFunctor C n).map e.inv)
    refine ⟨f ≫ e.hom, ?_⟩
    simp [derivedSingleHomologyMap_naturality, hf, ← Functor.map_comp]

/-- The projective-source Hom-to-homology computation, as an equivalence of abelian groups. -/
def projectiveSingleHomEquiv (A : C) [Projective A] (n : ℤ) (Y : DerivedCategory C) :
    ((DerivedCategory.singleFunctor C n).obj A ⟶ Y) ≃+
      (A ⟶ (DerivedCategory.homologyFunctor C n).obj Y) :=
  AddEquiv.ofBijective
    ({ toFun := derivedSingleHomologyMap A n Y
       map_zero' := by simp [derivedSingleHomologyMap]
       map_add' := by intro f g; simp [derivedSingleHomologyMap, Functor.map_add, comp_add] } :
      ((DerivedCategory.singleFunctor C n).obj A ⟶ Y) →+
        (A ⟶ (DerivedCategory.homologyFunctor C n).obj Y))
    (derivedSingleHomologyMap_bijective A n Y)

@[reassoc]
theorem projectiveSingleHomEquiv_naturality (A : C) [Projective A] (n : ℤ)
    {Y Z : DerivedCategory C} (f : (DerivedCategory.singleFunctor C n).obj A ⟶ Y)
    (g : Y ⟶ Z) :
    projectiveSingleHomEquiv A n Z (f ≫ g) =
      projectiveSingleHomEquiv A n Y f ≫ (DerivedCategory.homologyFunctor C n).map g :=
  derivedSingleHomologyMap_naturality A n f g

end ProjectiveSingle
end CWSolid
