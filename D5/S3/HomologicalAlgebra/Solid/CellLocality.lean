/- GID: D5/S3/HomologicalAlgebra/Solid/CellLocality
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/CellLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.CellFactorization
import D5.S3.HomologicalAlgebra.Solid.FreeFlat
import D5.S3.HomologicalAlgebra.Solid.FreeDetect

/-!
Locality of the actual unbounded cellular colimit.  These are new proofs
over the official Mathlib pin and the protected defining maps.
Released under the Apache 2.0 license.
-/

noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex
open CochainComplex HomComplex
attribute [local simp] CochainComplex.singleFunctors
open scoped ZeroObject

namespace LightCondensed.Solid

set_option backward.isDefEq.respectTransparency false in
private theorem cellular_component_boundaries
    (K : CochainComplex LightCondAb ℤ) (s : SmallModel.{0} LightProfinite) (n : ℤ)
    (a : P ⊗ (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed ⟶
      (solidCellularColimit K).X (n - 1))
    (b : P ⊗ (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed ⟶
      (solidCellularColimit K).X n)
    (hab : a ≫ (solidCellularColimit K).d (n - 1) n = (oneMinusShift ▷ _) ≫ b)
    (hb : b ≫ (solidCellularColimit K).d n (n + 1) = 0) :
    ∃ (x : P ⊗ (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed ⟶
        (solidCellularColimit K).X (n - 2))
      (y : P ⊗ (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed ⟶
        (solidCellularColimit K).X (n - 1)),
      a = (oneMinusShift ▷ _) ≫ y + x ≫ (solidCellularColimit K).d (n - 2) (n - 1) ∧
      b = y ≫ (solidCellularColimit K).d (n - 1) n := by
  let A := P ⊗ (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed
  let f : A ⟶ A := oneMinusShift ▷ _
  let T := solidCellularColimit K
  let B := (singleFunctor LightCondAb n).obj A
  let φ := (singleFunctor LightCondAb n).map f
  let β : B ⟶ T := mkHomFromSingle b (fun j hj => by
    have : j = n + 1 := by simpa using hj.symm
    subst j
    exact hb)
  have hdesc : δ (-1) 0 (Cochain.fromSingleMk a (by omega)) =
      Cochain.ofHom (φ ≫ β) := by
    apply (Cochain.fromSingleEquiv (add_zero n)).injective
    simp only [Cochain.δ_fromSingleMk a (show n + -1 = n - 1 by omega)
      0 n (add_zero n)]
    rw [Cochain.fromSingleEquiv_fromSingleMk]
    simpa [Cochain.fromSingleEquiv, β, φ, singleFunctor,
      single_map_f_self, mkHomFromSingle_f] using hab
  let g : mappingCone φ ⟶ T :=
    mappingCone.desc φ (Cochain.fromSingleMk a (by omega)) β hdesc
  let h : Homotopy g 0 := solidCellularColimit_cellMapHomotopy K (s, n) g
  let e := (singleObjXSelf (.up ℤ) n A).inv
  let x := e ≫ (mappingCone.inl φ).v n (n - 1) (by omega) ≫ h.hom (n - 1) (n - 2)
  let y := e ≫ (mappingCone.inr φ).f n ≫ h.hom n (n - 1)
  have hg₀ : e ≫ (mappingCone.inl φ).v n (n - 1) (by omega) ≫ g.f (n - 1) = a := by
    simp [g, e, mappingCone.inl_v_desc_f, Cochain.fromSingleMk_v]
  have hg₁ : e ≫ (mappingCone.inr φ).f n ≫ g.f n = b := by
    simp [g, e, β, mappingCone.inr_f_desc_f, mkHomFromSingle_f]
  refine ⟨x, y, ?_, ?_⟩
  · rw [← hg₀, h.comm]
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by change n - 1 + 1 = n; omega),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 2) (n - 1) by change n - 2 + 1 = n - 1; omega)]
    dsimp [x, y]
    simp only [add_zero, Preadditive.comp_add, Category.assoc]
    rw [mappingCone.inl_v_d_assoc φ n (n - 1) (n + 1) (by omega) (by omega)]
    simp [φ, singleFunctor, single_map_f_self, e, Category.assoc, f, T]
  · rw [← hg₁, h.comm]
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by change n - 1 + 1 = n; omega)]
    dsimp [y]
    simp only [add_zero, Preadditive.comp_add, Category.assoc]
    rw [mappingCone.inr_f_d_assoc]
    simp [singleFunctor, e, T]

private lemma uncurryP_zero {B X : LightCondAb} :
    uncurry (0 : B ⟶ (ihom P).obj X) = 0 :=
  (ihom.adjunction P).homAddEquiv_symm_zero B X

private lemma uncurryP_add {B X : LightCondAb} (a b : B ⟶ (ihom P).obj X) :
    uncurry (a + b) = uncurry a + uncurry b :=
  (ihom.adjunction P).homAddEquiv_symm_add B X a b

private lemma uncurryP_neg {B X : LightCondAb} (a : B ⟶ (ihom P).obj X) :
    uncurry (-a) = -uncurry a :=
  (ihom.adjunction P).homAddEquiv_symm_neg B X a

set_option backward.isDefEq.respectTransparency false in
private theorem cellular_defect_boundary_small
    (K : CochainComplex LightCondAb ℤ) (s : SmallModel.{0} LightProfinite) (n : ℤ)
    (t : (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed ⟶
      (solidComplexDefect (solidCellularColimit K)).X (n - 1))
    (ht : t ≫ (solidComplexDefect (solidCellularColimit K)).d (n - 1) n = 0) :
    ∃ u : (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed ⟶
        (solidComplexDefect (solidCellularColimit K)).X (n - 2),
      u ≫ (solidComplexDefect (solidCellularColimit K)).d (n - 2) (n - 1) = t := by
  let T := solidCellularColimit K
  let B : LightCondAb := (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed
  let I := (ihom P).mapHomologicalComplex (.up ℤ) |>.obj T
  let φ := solidComplexEndomorphism.app T
  change B ⟶ (mappingCone φ).X (n - 1) at t
  change t ≫ (mappingCone φ).d (n - 1) n = 0 at ht
  change ∃ u : B ⟶ (mappingCone φ).X (n - 2),
    u ≫ (mappingCone φ).d (n - 2) (n - 1) = t
  let p := t ≫ (mappingCone.fst φ).1.v (n - 1) n (by omega)
  let q := t ≫ (mappingCone.snd φ).v (n - 1) (n - 1) (add_zero _)
  have hp : p ≫ I.d n (n + 1) = 0 := by
    have h := congrArg (fun z => z ≫ (mappingCone.fst φ).1.v n (n + 1) rfl) ht
    rw [Category.assoc, mappingCone.d_fst_v φ (n - 1) n (n + 1)
      (by omega) rfl] at h
    simpa [p, I] using h
  have hq : p ≫ φ.f n + q ≫ I.d (n - 1) n = 0 := by
    have h := congrArg (fun z => z ≫ (mappingCone.snd φ).v n n (add_zero _)) ht
    rw [Category.assoc, mappingCone.d_snd_v φ (n - 1) n (by omega)] at h
    simpa [p, q, I, Preadditive.comp_add, Category.assoc] using h
  let a := -uncurry q
  let b := uncurry p
  have hq' : (oneMinusShift ▷ B) ≫ b + uncurry q ≫ T.d (n - 1) n = 0 := by
    change p ≫ (MonoidalClosed.pre oneMinusShift).app (T.X n) +
      q ≫ (ihom P).map (T.d (n - 1) n) = 0 at hq
    have h := congrArg (fun z => uncurry z) hq
    simpa only [uncurryP_add, uncurryP_zero, uncurry_pre_app,
      uncurry_natural_right] using h
  have hab : a ≫ T.d (n - 1) n = (oneMinusShift ▷ B) ≫ b := by
    dsimp only [a]
    rw [Preadditive.neg_comp]
    exact (eq_neg_of_add_eq_zero_left hq').symm
  have hb : b ≫ T.d n (n + 1) = 0 := by
    change p ≫ (ihom P).map (T.d n (n + 1)) = 0 at hp
    have h := congrArg (fun z => uncurry z) hp
    simpa only [uncurry_natural_right, uncurryP_zero] using h
  obtain ⟨x, y, ha, hy⟩ := cellular_component_boundaries K s n a b hab hb
  let u : B ⟶ (mappingCone φ).X (n - 2) :=
    curry (-y) ≫ (mappingCone.inl φ).v (n - 1) (n - 2) (by omega) +
      curry (-x) ≫ (mappingCone.inr φ).f (n - 2)
  have hu₁ : u ≫ (mappingCone.fst φ).1.v (n - 2) (n - 1) (by omega) = curry (-y) := by
    simp [u, Preadditive.add_comp]
    rfl
  have hu₂ : u ≫ (mappingCone.snd φ).v (n - 2) (n - 2) (add_zero _) = curry (-x) := by
    simp [u, Preadditive.add_comp]
    rfl
  refine ⟨u, ?_⟩
  apply mappingCone.ext_to φ (n - 1) n (by omega)
  · rw [Category.assoc, mappingCone.d_fst_v φ (n - 2) (n - 1) n (by omega) (by omega)]
    simp only [Preadditive.comp_neg, ← Category.assoc, hu₁]
    apply uncurry_injective
    change uncurry (-(curry (-y) ≫ (ihom P).map (T.d (n - 1) n))) = b
    simp only [uncurryP_neg, uncurry_natural_right, uncurry_curry,
      Preadditive.neg_comp, neg_neg]
    exact hy.symm
  · rw [Category.assoc, mappingCone.d_snd_v φ (n - 2) (n - 1) (by omega)]
    simp only [Preadditive.comp_add, ← Category.assoc, hu₁, hu₂]
    apply uncurry_injective
    change uncurry (curry (-y) ≫ (MonoidalClosed.pre oneMinusShift).app (T.X (n - 1)) +
      curry (-x) ≫ (ihom P).map (T.d (n - 2) (n - 1))) = uncurry q
    simp only [uncurryP_add, uncurry_pre_app, uncurry_natural_right, uncurry_curry]
    have h := congrArg Neg.neg ha
    simpa only [a, neg_add, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Every cycle of the internal-Hom defect, tested by any light profinite
generator, is an actual boundary.  All integer degrees are covered. -/
theorem solidCellularColimit_defect_boundaries
    (K : CochainComplex LightCondAb ℤ) (S : LightProfinite) (m : ℤ)
    (t : (free ℤ).obj S.toCondensed ⟶ (solidComplexDefect (solidCellularColimit K)).X m)
    (ht : t ≫ (solidComplexDefect (solidCellularColimit K)).d m (m + 1) = 0) :
    ∃ u : (free ℤ).obj S.toCondensed ⟶ (solidComplexDefect (solidCellularColimit K)).X (m - 1),
      u ≫ (solidComplexDefect (solidCellularColimit K)).d (m - 1) m = t := by
  let E : LightProfinite ≌ SmallModel.{0} LightProfinite := equivSmallModel LightProfinite
  let s := E.functor.obj S
  let e := (lightProfiniteToLightCondSet ⋙ free ℤ).mapIso (E.unitIso.app S).symm
  have h : ∀ t : (free ℤ).obj (E.inverse.obj s).toCondensed ⟶
      (solidComplexDefect (solidCellularColimit K)).X m,
      t ≫ (solidComplexDefect (solidCellularColimit K)).d m (m + 1) = 0 →
      ∃ u : (free ℤ).obj (E.inverse.obj s).toCondensed ⟶
          (solidComplexDefect (solidCellularColimit K)).X (m - 1),
        u ≫ (solidComplexDefect (solidCellularColimit K)).d (m - 1) m = t := by
    have hh := cellular_defect_boundary_small K s (m + 1)
    rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega] at hh
    exact hh
  obtain ⟨u, hu⟩ := h (e.hom ≫ t) (by rw [Category.assoc, ht, comp_zero])
  refine ⟨e.inv ≫ u, ?_⟩
  rw [Category.assoc, hu, e.inv_hom_id_assoc]

/-- The complete unbounded cellular colimit has zero locality defect. -/
theorem solidCellularColimit_defect_acyclic (K : CochainComplex LightCondAb ℤ) :
    (solidComplexDefect (solidCellularColimit K)).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  exact exact_of_free_boundaries _ (fun S t ht =>
    solidCellularColimit_defect_boundaries K S n t ht)

/-- The cellular colimit is derived-local in every integer degree. This is
locality of an actual construction, with no assumed replacement theorem. -/
theorem solidCellularColimit_homology_solid (K : CochainComplex LightCondAb ℤ) (n : ℤ) :
    isSolid ((solidCellularColimit K).homology n) := by
  let D := solidComplexDefect (solidCellularColimit K)
  let z : D ⟶ (0 : CochainComplex LightCondAb ℤ) := 0
  have : QuasiIso z := by
    rw [quasiIso_iff]
    intro m
    apply (quasiIsoAt_iff_exactAt' z m ?_).2 (solidCellularColimit_defect_acyclic K m)
    exact HomologicalComplex.ExactAt.of_isZero
      ((eval LightCondAb (.up ℤ) m).map_isZero
        (Limits.isZero_zero (CochainComplex LightCondAb ℤ)))
  have hz : IsZero (DerivedCategory.Q.obj D) :=
    (DerivedCategory.Q.map_isZero (Limits.isZero_zero (CochainComplex LightCondAb ℤ))).of_iso
      (asIso (DerivedCategory.Q.map z))
  exact ((isZero_solidComplexDefect_iff (solidCellularColimit K)).1 hz) n

end LightCondensed.Solid
