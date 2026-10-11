/- GID: D5/S3/HomologicalAlgebra/Solid/CellFactorization
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/CellFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.CellularSolidification

/-! Finite-stage factorization for the concrete two-term localization cells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex
open CochainComplex HomComplex
attribute [local simp] CochainComplex.singleFunctors

namespace LightCondensed.Solid

private def cellMapFrom {A : LightCondAb} (f : A ⟶ A) (n : ℤ)
    {K : CochainComplex LightCondAb ℤ} (a : A ⟶ K.X (n - 1)) (b : A ⟶ K.X n)
    (hab : a ≫ K.d (n - 1) n = f ≫ b) (hb : b ≫ K.d n (n + 1) = 0) :
    mappingCone ((singleFunctor LightCondAb n).map f) ⟶ K := by
  let β : (singleFunctor LightCondAb n).obj A ⟶ K :=
    mkHomFromSingle b (fun j hj => by
      have : j = n + 1 := by simpa using hj.symm
      subst j
      exact hb)
  refine mappingCone.desc _ (Cochain.fromSingleMk a (by omega)) β ?_
  apply (Cochain.fromSingleEquiv (add_zero n)).injective
  simp only [Cochain.δ_fromSingleMk a (show n + -1 = n - 1 by omega)
    0 n (add_zero n)]
  rw [Cochain.fromSingleEquiv_fromSingleMk]
  change a ≫ K.d (n - 1) n = _
  simpa [Cochain.fromSingleEquiv, β, singleFunctor,
    HomologicalComplex.single_map_f_self, HomologicalComplex.mkHomFromSingle_f] using hab

private theorem cellMap_ext {A : LightCondAb} (f : A ⟶ A) (n : ℤ)
    {K : CochainComplex LightCondAb ℤ}
    {g h : mappingCone ((singleFunctor LightCondAb n).map f) ⟶ K}
    (ha : (HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫
        (mappingCone.inl ((singleFunctor LightCondAb n).map f)).v n (n - 1) (by omega) ≫ g.f (n - 1) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫
        (mappingCone.inl ((singleFunctor LightCondAb n).map f)).v n (n - 1) (by omega) ≫ h.f (n - 1))
    (hb : (HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫
        (mappingCone.inr ((singleFunctor LightCondAb n).map f)).f n ≫ g.f n =
      (HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫
        (mappingCone.inr ((singleFunctor LightCondAb n).map f)).f n ≫ h.f n) : g = h := by
  ext k : 1
  by_cases hk : k = n - 1
  · subst k
    apply mappingCone.ext_from _ n (n - 1) (by omega)
    · exact (cancel_epi (singleObjXSelf (.up ℤ) n A).inv).1 ha
    · exact (isZero_single_obj_X (.up ℤ) n A (n - 1) (by omega)).eq_of_src _ _
  · by_cases hk' : k = n
    · subst k
      apply mappingCone.ext_from _ (n + 1) n rfl
      · exact (isZero_single_obj_X (.up ℤ) n A (n + 1) (by omega)).eq_of_src _ _
      · exact (cancel_epi (singleObjXSelf (.up ℤ) n A).inv).1 hb
    · apply mappingCone.ext_from _ (k + 1) k rfl
      · exact (isZero_single_obj_X (.up ℤ) n A (k + 1) (by omega)).eq_of_src _ _
      · exact (isZero_single_obj_X (.up ℤ) n A k hk').eq_of_src _ _

attribute [local instance] Cardinal.fact_isRegular_aleph0

private theorem factorCellComponents {A : LightCondAb}
    [IsCardinalPresentable A Cardinal.aleph0] (f : A ⟶ A) (n : ℤ)
    (F : ℕ ⥤ CochainComplex LightCondAb ℤ)
    (a₀ : A ⟶ (colimit F).X (n - 1)) (b₀ : A ⟶ (colimit F).X n)
    (hab₀ : a₀ ≫ (colimit F).d (n - 1) n = f ≫ b₀)
    (hb₀ : b₀ ≫ (colimit F).d n (n + 1) = 0) :
    ∃ (k : ℕ) (a : A ⟶ (F.obj k).X (n - 1)) (b : A ⟶ (F.obj k).X n),
      a ≫ (F.obj k).d (n - 1) n = f ≫ b ∧ b ≫ (F.obj k).d n (n + 1) = 0 ∧
      a ≫ (colimit.ι F k).f (n - 1) = a₀ ∧ b ≫ (colimit.ι F k).f n = b₀ := by
  haveI : IsCardinalFiltered ℕ Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff ℕ).2 inferInstance
  let H r := isColimitOfPreserves (eval LightCondAb (.up ℤ) r) (colimit.isColimit F)
  have hw {k l : ℕ} (u : k ⟶ l) (r : ℤ) :
      (F.map u).f r ≫ (colimit.ι F l).f r = (colimit.ι F k).f r := by
    exact congrArg (fun q => q.f r) (colimit.w F u)
  obtain ⟨k₀, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    Cardinal.aleph0 (H (n - 1)) a₀
  obtain ⟨k₁, b, hb⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    Cardinal.aleph0 (H n) b₀
  change A ⟶ (F.obj k₀).X (n - 1) at a
  change a ≫ (colimit.ι F k₀).f (n - 1) = a₀ at ha
  change A ⟶ (F.obj k₁).X n at b
  change b ≫ (colimit.ι F k₁).f n = b₀ at hb
  let k := max k₀ k₁
  let a₁ := a ≫ (F.map (homOfLE (le_max_left k₀ k₁))).f (n - 1)
  let b₁ := b ≫ (F.map (homOfLE (le_max_right k₀ k₁))).f n
  have ha₁ : a₁ ≫ (colimit.ι F k).f (n - 1) = a₀ := by
    dsimp [a₁, k]
    rw [Category.assoc, hw]
    exact ha
  have hb₁ : b₁ ≫ (colimit.ι F k).f n = b₀ := by
    dsimp [b₁, k]
    rw [Category.assoc, hw]
    exact hb
  have heq : (a₁ ≫ (F.obj k).d (n - 1) n) ≫ (colimit.ι F k).f n =
      (f ≫ b₁) ≫ (colimit.ι F k).f n := by
    rw [Category.assoc, ← (colimit.ι F k).comm, ← Category.assoc, ha₁,
      hab₀, Category.assoc, hb₁]
  obtain ⟨l, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
    Cardinal.aleph0 (H n) (a₁ ≫ (F.obj k).d (n - 1) n) (f ≫ b₁) heq
  change (a₁ ≫ (F.obj k).d (n - 1) n) ≫ (F.map u).f n =
    (f ≫ b₁) ≫ (F.map u).f n at hu
  let a₂ := a₁ ≫ (F.map u).f (n - 1)
  let b₂ := b₁ ≫ (F.map u).f n
  have hab₂ : a₂ ≫ (F.obj l).d (n - 1) n = f ≫ b₂ := by
    dsimp [a₂, b₂]
    rw [Category.assoc, (F.map u).comm]
    simpa [Category.assoc] using hu
  have ha₂ : a₂ ≫ (colimit.ι F l).f (n - 1) = a₀ := by
    dsimp [a₂]
    rw [Category.assoc, hw]
    exact ha₁
  have hb₂ : b₂ ≫ (colimit.ι F l).f n = b₀ := by
    dsimp [b₂]
    rw [Category.assoc, hw]
    exact hb₁
  have heq' : (b₂ ≫ (F.obj l).d n (n + 1)) ≫ (colimit.ι F l).f (n + 1) =
      (0 : A ⟶ (F.obj l).X (n + 1)) ≫ (colimit.ι F l).f (n + 1) := by
    rw [Category.assoc, ← (colimit.ι F l).comm, ← Category.assoc, hb₂, hb₀, zero_comp]
  obtain ⟨m, v, hv⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
    Cardinal.aleph0 (H (n + 1)) (b₂ ≫ (F.obj l).d n (n + 1)) 0 heq'
  change (b₂ ≫ (F.obj l).d n (n + 1)) ≫ (F.map v).f (n + 1) =
    (0 : A ⟶ (F.obj l).X (n + 1)) ≫ (F.map v).f (n + 1) at hv
  refine ⟨m, a₂ ≫ (F.map v).f (n - 1), b₂ ≫ (F.map v).f n, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, (F.map v).comm, ← Category.assoc, hab₂, Category.assoc]
  · rw [Category.assoc, (F.map v).comm, ← Category.assoc]
    simpa using hv
  · rw [Category.assoc, hw]
    exact ha₂
  · rw [Category.assoc, hw]
    exact hb₂

set_option backward.isDefEq.respectTransparency false in
/-- Every chain map from a defining two-term cell into the full cellular
colimit factors through an actual finite stage.  The incoming complex is
arbitrary and unbounded. -/
theorem solidCellularColimit_cellMap_factors
    (K : CochainComplex LightCondAb ℤ) (i : SmallModel.{0} LightProfinite × ℤ)
    (g : solidLocalizationCell i ⟶ solidCellularColimit K) :
    ∃ (k : ℕ) (g' : solidLocalizationCell i ⟶ solidCellularStage K k),
      g' ≫ colimit.ι (solidCellularDiagram K) k = g := by
  let S := (equivSmallModel LightProfinite).inverse.obj i.1
  let A := P ⊗ (free ℤ).obj S.toCondensed
  let f : A ⟶ A := oneMinusShift ▷ (free ℤ).obj S.toCondensed
  let n := i.2
  haveI : IsCardinalPresentable A Cardinal.aleph0 := by
    have := LightSolidFilteredScaffold.preservesFilteredColimits_hom_P_tensor_free S
    constructor
    intro J _ _
    have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
    infer_instance
  let φ := (singleFunctor LightCondAb n).map f
  change mappingCone φ ⟶ solidCellularColimit K at g
  let a₀ := (singleObjXSelf (.up ℤ) n A).inv ≫
    (mappingCone.inl φ).v n (n - 1) (by omega) ≫ g.f (n - 1)
  let b₀ := (singleObjXSelf (.up ℤ) n A).inv ≫ (mappingCone.inr φ).f n ≫ g.f n
  have hab₀ : a₀ ≫ (solidCellularColimit K).d (n - 1) n = f ≫ b₀ := by
    dsimp [a₀, b₀]
    simp only [Category.assoc]
    rw [g.comm,
      mappingCone.inl_v_d_assoc φ n (n - 1) (n + 1) (by omega) (by omega)]
    simp [φ, singleFunctor, HomologicalComplex.single_map_f_self, Category.assoc]
  have hb₀ : b₀ ≫ (solidCellularColimit K).d n (n + 1) = 0 := by
    dsimp [b₀]
    simp only [Category.assoc]
    rw [g.comm, mappingCone.inr_f_d_assoc]
    simp [φ, singleFunctor]
  obtain ⟨k, a, b, hab, hb, ha, hb'⟩ :=
    factorCellComponents f n (solidCellularDiagram K) a₀ b₀ hab₀ hb₀
  let g' := cellMapFrom f n a b hab hb
  have hg₀ : (singleObjXSelf (.up ℤ) n A).inv ≫
      (mappingCone.inl φ).v n (n - 1) (by omega) ≫ g'.f (n - 1) = a := by
    unfold g' cellMapFrom φ
    simp only [Category.assoc, mappingCone.inl_v_desc_f, Cochain.fromSingleMk_v,
      Iso.inv_hom_id_assoc]
  have hg₁ : (singleObjXSelf (.up ℤ) n A).inv ≫
      (mappingCone.inr φ).f n ≫ g'.f n = b := by
    unfold g' cellMapFrom φ
    simp only [Category.assoc, mappingCone.inr_f_desc_f, mkHomFromSingle_f,
      Iso.inv_hom_id_assoc]
  refine ⟨k, g', ?_⟩
  apply cellMap_ext f n
  · change (singleObjXSelf (.up ℤ) n A).inv ≫
        (mappingCone.inl φ).v n (n - 1) (by omega) ≫
          (g' ≫ colimit.ι (solidCellularDiagram K) k).f (n - 1) = a₀
    rw [HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc]
    rw [show ((singleObjXSelf (.up ℤ) n A).inv ≫
      (mappingCone.inl φ).v n (n - 1) (by omega)) ≫ g'.f (n - 1) = a from
        (by simpa only [Category.assoc] using hg₀)]
    exact ha
  · change (singleObjXSelf (.up ℤ) n A).inv ≫ (mappingCone.inr φ).f n ≫
        (g' ≫ colimit.ι (solidCellularDiagram K) k).f n = b₀
    rw [HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc]
    rw [show ((singleObjXSelf (.up ℤ) n A).inv ≫ (mappingCone.inr φ).f n) ≫ g'.f n = b from
      (by simpa only [Category.assoc] using hg₁)]
    exact hb'

/-- Every defining-cell map into the cellular colimit is null-homotopic,
not merely those initially supplied at a chosen finite stage. -/
def solidCellularColimit_cellMapHomotopy
    (K : CochainComplex LightCondAb ℤ) (i : SmallModel.{0} LightProfinite × ℤ)
    (g : solidLocalizationCell i ⟶ solidCellularColimit K) : Homotopy g 0 := by
  let h := solidCellularColimit_cellMap_factors K i g
  exact (Homotopy.ofEq h.choose_spec.choose_spec.symm).trans
    (solidCellularColimitHomotopy K h.choose i h.choose_spec.choose)

end LightCondensed.Solid
