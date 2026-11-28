/- GID: D5/S3/Zeros/GRH/New/Selmer/BaseLevelOfLabel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/BaseLevelOfLabel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.BaseLevelOfLabel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/BaseLevelOfLabel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.TaylorWiles.HeckeAlgebra
import D5.S3.Zeros.GRH.New.Trace.LabelRigidity
import D5.S3.Zeros.GRH.New.Selmer.LabelledColumns
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: An auxiliary pair with apt labels c gives a `BaseLevel` of forms containing the image of
the idempotent of c. -/
seal Finset.univ Finset.sum Finset.prod

open Space

attribute [-simp] Set.Sum.elim_range

attribute [local simp] Finsupp.sum MonoidAlgebra.lift_apply Representation.asAlgebraHom_def
  twistedLabel

/-- For apt c and auxiliary Q, some `BaseLevel` over the integers of ℚ̄_ℓ contains im e_c, with
Mk·e_c preserving integrality (Mk = `Data.chosenGroupOrder`, e_c = `tupleProj`);
its eigensystems at finite levels u off `badPlaces` D ℓ give
normalised representations R that are `IsLabelledColumn` of one jump type, with (R − a)(R − 1) = 0
on inertia above Q ∪ Q̄, a the avatar of ϑ⁻¹. -/
lemma exists_baseLevel {ℓ} [ThePrime ℓ] [PadicIso ℓ] {P} {D : Data P} {r n} [Fintype r] [Fintype n]
  {O : AuxPair _ r n} [Nonempty n] {ϑ c} (h : IsApt O c ϑ) (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) :
  ∃ J, ∃ B : BaseLevel _ _ D.chosenGroupOrder, (∀ y ∈ (tupleProj O c).range, y.toSmoothForm ∈
  B.formsOfLevel ![]) ∧ (∀ y, y.toSmoothForm ∈ BaseLevel.ellIntegralForms → D.chosenGroupOrder •
  (tupleProj O c y).toSmoothForm ∈ BaseLevel.ellIntegralForms) ∧ ∀ K [Finite K] u,
  (∀ k, u k ∉ badPlaces D ℓ) → ∀ x ∈ B.Eigensystem (J := K) u, let R := normalisedRep O x.galRep;
    IsLabelledColumn O O.rankDiff J (twistedLabel O c · * (.X - 1) ^ O.rankDiff) (.conjClosure ϑ.Q ∪
    (Set.range u).conjClosure) R ∧ ∀ g ∈ inertiaAbove (.conjClosure ϑ.Q),
    ((R g).1 - ϑ.invAvatar g • 1) * ((R g).1 - 1) = 0 := let π :=
    ((stdSpace _ n).formTranslation (O.κ, O.detExp)).comp (Gf.componentOn n O.places.toFinset)
  have hπ {k} (h : k ∈ Gf.supportedOn n O.places) : π k = formTranslation _ _ k :=
    congrArg (formTranslation ..) (Gf.ext (by simp_all))
  let ρ := (O.chosenGLRep π).asAlgebraHom (tupleIdem r c)
  have hρ u := (show (ρ u).1 = _ by simp [ρ, AuxPair.chosenGLRep, levelRep]; rfl :)
  let j (y : O.FormV) : levelSpace π _ O.levelChar := ⟨y.toSmoothForm, fun k ↦
    congr(⟨$(levelSpace_levelOf_apply y.2 ⟨_, Gf.componentOn_mem_Kf (levelOf_le_Kf k.2)⟩ _ (funext
    fun j ↦ (Kf.reduceAt _).div_mem_ker_iff.1 (Kf.reduceAt_eq_one_of_atPlace (by simp)))), _⟩)⟩
  have hj y : (ρ (j y)).1 = (tupleProj O c y).toSmoothForm := by
    simp [hρ, tupleProj, AuxPair.groupAlgAction, hπ (liftResidue_mem_supportedOn _)]; rfl
  ⟨_, (⟨_, (ρ.eqLocus 1).map (Submodule.subtype _), fun T hT _ ⟨u, e, a⟩ ↦
    a ▸ ⟨⟨_, map_mem_levelSpace_of_commute u.2 (hT ⟨_, levelOf_le_Kf ·.2⟩)⟩, Subtype.ext (by
    simpa [hρ, π, ← Module.End.mul_apply, (hT _).eq, -Set.coe_toFinset, -Set.toFinset_range] using
      congr(T $e)), rfl⟩, ⟨_, _, isOpen_levelOf, Submodule.map_subtype_le ..⟩,
    D.card_classAut_dvd_chosenGroupOrder h.card_le le_rfl⟩ : BaseLevel ..), fun y m ↦ ⟨⟨j y,
    Subtype.ext ((hj y).trans congr($(IsApt.tupleProj_eq_self_of_mem_range m).toSmoothForm)), rfl⟩,
    fun k ↦ .trans congr(⟨$(y.algFormRep_eq_self_of_mem
    (inf_trivialOn_le_levelOf ⟨Gf.componentOn_mem_Kf (levelOf_le_Kf k.2), by simp_all⟩)), _⟩)
    (one_smul ..).symm⟩, fun y hy x m ↦ (h.1 ▸ D.card_GL_dvd_chosenGroupOrder (h.rank_le.1.trans
    D.nat_le_of_hasLogBound) : .card (O.ChosenGL r) ∣ D.chosenGroupOrder).elim fun t e
    i ↦ by simpa [← hj, hρ, e, Finset.mul_sum, mul_assoc, mul_left_comm _ (t :
    ℂ)] using! (sum_mem fun g _ ↦ mul_mem (by simp) (mul_mem (norm_le_one_of_isIntegral ιℓ.toRingHom
    ((isCentralProj_tupleIdem c).isChar.isIntegral g)) (mul_mem
    (ιℓ.toRingHom.isOfFinOrder (O.isOfFinOrder_prod_psi_det g)).norm_eq_one.le
    (hy _ (mul_mem m (Kf_le_localLevel (Gf.componentOn_mem_Kf (by simp)))) i)))), by
  rintro _ _ U hX x ⟨_, ⟨b, hf⟩, h₀⟩
  obtain ⟨⟨u, a, rfl⟩, he, hR⟩ := hf.1, x.isEigenform b h₀, x.attached_galRep b h₀
  have A j k := hπ (Gf.supportedOn_mono (by simp) (atSplit_mem_supportedOn (O.apart.2 j j) k))
  set_option backward.isDefEq.respectTransparency false in
    refine ⟨by simpa using! ((isLabelledColumn_of_hasProductLabel h u.1.2 he hR (fun v m k
      g ↦ congr($(And.elim levelSpace_le_sphericalAt (by simp; clear * - m k hX h hQ; grind [(h.1 ▸
      Subtype.range_coe : Set.range O.twistPlace = ϑ.Q)]) (BaseLevel.formsOfLevel_le_levelSpace hf)
      g))) fun i ↦ HasParahoricType.hasProductLabel ((forms ..).subtype.domRestrict _) (by simp)
      (a.trans_ne (h₀ ∘ congrArg _) <| piTensorElem_apply_eq_zero i ·)
      (D.hasParahoricType_chosenGLRep (A (.inl i) · ▸ rfl)) (.of_lt_imp_ne (by simp))
      (by simpa using h.isLabel_twistedLabel i)).twist_avatar (.inv (μ := O.a)) _ _ (by
      clear * -; grind only [O.rank_lt]) h (by simp)), normalisedRep_quadratic_on_inertia h hQ he hR
      fun i ↦ ⟨?_, fun k _ a _ ↦ congr($(A _ _ ▸ levelSpace_levelOf_apply u.2 _ ⟨_,
      (Subgroup.mulSingle_mem_pi ..).2 fun _ ↦ (mem_rangeParabolic_iff _).2 fun _ _ _ ↦
      a ?_⟩ (reduceFamily_atSplit ..)).1).trans ?_⟩⟩ <;> open Calc in simp +contextual [*,
      AuxPair.auxLevelChar, Fintype.prod_eq_single i, MulChar.one_apply, ite_eq_iff]
    rw [← Matrix.det_submatrix_equiv_self (O.incl.toEquivRange.trans (.subtypeEquivProp
      (by open Calc in simp)))]; rfl⟩
