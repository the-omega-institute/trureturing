/- GID: D5/S3/Factorization/Galois/GaloisCompatibleFiberProduct
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GaloisCompatibleFiberProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Galois composita are compatible fiber products; edge cases are audited. -/
/- Library-search audit trail (2026-08-29):
   * Mathematical-name searches covered composita, pullbacks, fiber products, and gluing.
   * Pinned Mathlib has no packaged Galois fiber-product equivalence or gluing theorem.
   * Exact reusable hits were `IntermediateField.extendScalars_inf`,
     `IntermediateField.restrictRestrictAlgEquivMapHom_surjective`, and
     `IntermediateField.fixingSubgroup_sup`; the proof below combines them over the intersection.
   * Digest search found `row/Galois-复合域-fiber-product` open with no coverage GID.
   * Repository search found only `joint_restriction_lands_in_fiber_product` and the
     trivial-intersection product theorem in `GaloisFusion`; neither is the general isomorphism.
   * The two source corollaries are already covered by those named public theorems. -/

import D5.S3.Factorization.Galois.GaloisFusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.GaloisCompatibleFiberProduct

open D5.S3.Factorization.Galois.GaloisFusion

/-- Joint restriction, with its shared-field compatibility included in the codomain. -/
noncomputable def compatibleRestriction
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂] :
    Gal(E/K) →*
      groupFiberProduct (restrictToSharedLeft L₁ L₂) (restrictToSharedRight L₁ L₂) where
  toFun sigma :=
    ⟨jointRestriction L₁ L₂ sigma, joint_restriction_lands_in_fiber_product L₁ L₂ sigma⟩
  map_one' := Subtype.ext (map_one (jointRestriction L₁ L₂))
  map_mul' sigma tau := Subtype.ext (map_mul (jointRestriction L₁ L₂) sigma tau)

private theorem restrictToSharedLeft_apply
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    (sigma : Gal(L₁/K)) (x : sharedField L₁ L₂) :
    ((restrictToSharedLeft L₁ L₂ sigma x : sharedField L₁ L₂) : E) =
      ((sigma ⟨x, x.property.1⟩ : L₁) : E) := by
  let S : IntermediateField K E := sharedField L₁ L₂
  let hS : S ≤ L₁ := by
    dsimp [S, sharedField]
    exact inf_le_left
  let T : IntermediateField K L₁ := S.restrict hS
  letI : Normal K S := by
    change Normal K (L₁ ⊓ L₂ : IntermediateField K E)
    infer_instance
  letI : Normal K T := Normal.of_algEquiv (S.restrict_algEquiv hS)
  let equiv : S ≃ₐ[K] T := S.restrict_algEquiv hS
  let y : T := (AlgEquiv.restrictNormalHom T sigma) (equiv x)
  change ((equiv.symm y : S) : E) = ((sigma ⟨x, x.property.1⟩ : L₁) : E)
  have htransport : ((equiv.symm y : S) : E) = ((y : T) : L₁) := by
    exact congrArg (fun z : T => ((z : L₁) : E)) (equiv.apply_symm_apply y)
  have hrestrict : ((y : T) : L₁) = sigma ((equiv x : T) : L₁) := by
    exact AlgEquiv.restrictNormal_commutes sigma T (equiv x)
  have hrestrictE : ((y : T) : L₁) = ((sigma ((equiv x : T) : L₁) : L₁) : E) :=
    congrArg (fun z : L₁ => ((z : L₁) : E)) hrestrict
  exact htransport.trans (hrestrictE.trans rfl)

private theorem compatibleRestriction_injective
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) : Function.Injective (compatibleRestriction L₁ L₂) := by
  intro sigma tau hst
  have hpair : jointRestriction L₁ L₂ sigma = jointRestriction L₁ L₂ tau :=
    congrArg Subtype.val hst
  have h₁ : ∀ y : L₁, sigma y = tau y := by
    intro y
    simpa [jointRestriction, AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Prod.fst hpair) y)
  have h₂ : ∀ y : L₂, sigma y = tau y := by
    intro y
    simpa [jointRestriction, AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Prod.snd hpair) y)
  have hfix₁ : tau⁻¹ * sigma ∈ L₁.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    simp only [AlgEquiv.mul_apply]
    rw [h₁ ⟨y, hy⟩]
    exact tau.symm_apply_apply y
  have hfix₂ : tau⁻¹ * sigma ∈ L₂.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    simp only [AlgEquiv.mul_apply]
    rw [h₂ ⟨y, hy⟩]
    exact tau.symm_apply_apply y
  have hfix : tau⁻¹ * sigma ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfix₁, hfix₂⟩
  rw [hsup, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hfix
  exact (inv_mul_eq_one.mp hfix).symm

private theorem compatibleRestriction_surjective
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [Normal K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) : Function.Surjective (compatibleRestriction L₁ L₂) := by
  let S : IntermediateField K E := sharedField L₁ L₂
  have hS₁ : S ≤ L₁ := by
    dsimp [S, sharedField]
    exact inf_le_left
  have hS₂ : S ≤ L₂ := by
    dsimp [S, sharedField]
    exact inf_le_right
  let L₁S : IntermediateField S E := IntermediateField.extendScalars hS₁
  let L₂S : IntermediateField S E := IntermediateField.extendScalars hS₂
  have hinfS : L₁S ⊓ L₂S = ⊥ := by
    dsimp only [L₁S, L₂S]
    rw [IntermediateField.extendScalars_inf]
    exact IntermediateField.extendScalars_self S
  have hsupS : L₁S ⊔ L₂S = ⊤ := by
    dsimp only [L₁S, L₂S]
    rw [IntermediateField.extendScalars_sup]
    apply IntermediateField.restrictScalars_injective K
    simpa using hsup
  let e₁ : L₁S ≃ₐ[K] L₁ :=
    IntermediateField.equivOfEq (IntermediateField.extendScalars_restrictScalars hS₁)
  let e₂ : L₂S ≃ₐ[K] L₂ :=
    IntermediateField.equivOfEq (IntermediateField.extendScalars_restrictScalars hS₂)
  letI : IsGalois K L₁S := IsGalois.of_algEquiv e₁.symm
  letI : FiniteDimensional K L₁S :=
    LinearEquiv.finiteDimensional e₁.toLinearEquiv.symm
  letI : FiniteDimensional K L₂S :=
    LinearEquiv.finiteDimensional e₂.toLinearEquiv.symm
  letI : IsGalois S L₁S := IsGalois.tower_top_of_isGalois K S L₁S
  letI : FiniteDimensional S L₁S := FiniteDimensional.right K S L₁S
  letI : FiniteDimensional S L₂S := FiniteDimensional.right K S L₂S
  have hdisjointS : L₁S.LinearDisjoint L₂S :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot hinfS
  have hrank : Module.finrank L₂S E = Module.finrank S L₁S :=
    hdisjointS.finrank_right_eq_finrank hsupS
  letI : FiniteDimensional L₂S E :=
    FiniteDimensional.of_finrank_pos (hrank.trans_gt Module.finrank_pos)
  letI : IsGalois L₂S E := IsGalois.sup_right L₁S L₂S hsupS
  letI : Normal K (⊤ : IntermediateField K E) :=
    hsup ▸ (inferInstance : Normal K (L₁ ⊔ L₂ : IntermediateField K E))
  letI : Normal K E := Normal.of_algEquiv IntermediateField.topEquiv
  rintro ⟨⟨a, b⟩, hab⟩
  obtain ⟨tau, htau⟩ := AlgEquiv.restrictNormalHom_surjective E b
  let tau₁ : Gal(L₁/K) := AlgEquiv.restrictNormalHom L₁ tau
  let delta : Gal(L₁/K) := a * tau₁⁻¹
  have htauCompatible := joint_restriction_lands_in_fiber_product L₁ L₂ tau
  have hsame : restrictToSharedLeft L₁ L₂ a = restrictToSharedLeft L₁ L₂ tau₁ := by
    apply hab.trans
    rw [← htau]
    exact htauCompatible.symm
  have hdelta : restrictToSharedLeft L₁ L₂ delta = 1 := by
    dsimp only [delta]
    rw [map_mul, map_inv, hsame, mul_inv_cancel]
  let deltaK : Gal(L₁S/K) := (AlgEquiv.autCongr e₁).symm delta
  let deltaS : Gal(L₁S/S) :=
    { deltaK.toRingEquiv with
      commutes' := by
        intro x
        apply Subtype.ext
        have hfixE : ((delta ⟨x, x.property.1⟩ : L₁) : E) = x := by
          calc
            ((delta ⟨x, x.property.1⟩ : L₁) : E) =
                ((restrictToSharedLeft L₁ L₂ delta x : S) : E) :=
              (restrictToSharedLeft_apply L₁ L₂ delta x).symm
            _ = x := congrArg Subtype.val (DFunLike.congr_fun hdelta x)
        change ((e₁.symm (delta (e₁ (algebraMap S L₁S x))) : L₁S) : E) = x
        have harg : e₁ (algebraMap S L₁S x) = (⟨x, x.property.1⟩ : L₁) := by
          apply Subtype.ext
          rfl
        rw [harg]
        calc
          ((e₁.symm (delta ⟨x, x.property.1⟩) : L₁S) : E) =
              ((delta ⟨x, x.property.1⟩ : L₁) : E) := rfl
          _ = x := hfixE }
  obtain ⟨phi, hphi⟩ :=
    IntermediateField.restrictRestrictAlgEquivMapHom_surjective L₁S L₂S hinfS deltaS
  let phiS : Gal(E/S) := phi.restrictScalars S
  let phiK : Gal(E/K) := phiS.restrictScalars K
  have hphi₁ : AlgEquiv.restrictNormalHom L₁ phiK = delta := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    let xS : L₁S := ⟨x, x.property⟩
    have hx := congrArg Subtype.val (DFunLike.congr_fun hphi xS)
    have hmap :=
      IntermediateField.restrictRestrictAlgEquivMapHom_apply L₁S L₂S phi xS
    have hxS : e₁ xS = x := by
      apply Subtype.ext
      rfl
    calc
      ((AlgEquiv.restrictNormalHom L₁ phiK x : L₁) : E) = phiK (x : E) :=
        AlgEquiv.restrictNormal_commutes phiK L₁ x
      _ = phi (x : E) := rfl
      _ = phi (xS : E) := rfl
      _ = (((IntermediateField.restrictRestrictAlgEquivMapHom S L₁S L₂S E) phi
          xS : L₁S) : E) := hmap.symm
      _ = ((deltaS xS : L₁S) : E) := hx
      _ = ((delta x : L₁) : E) := by
        dsimp only [deltaS, deltaK]
        change ((e₁.symm (delta (e₁ xS)) : L₁S) : E) = ((delta x : L₁) : E)
        rw [hxS]
        rfl
  have hphi₂ : AlgEquiv.restrictNormalHom L₂ phiK = 1 := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    let xS : L₂S := ⟨x, x.property⟩
    simpa [phiK, phiS, xS, AlgEquiv.restrictNormalHom_apply] using phi.commutes xS
  refine ⟨phiK * tau, Subtype.ext ?_⟩
  apply Prod.ext
  · change AlgEquiv.restrictNormalHom L₁ (phiK * tau) = a
    rw [map_mul, hphi₁]
    simp [delta, tau₁]
  · change AlgEquiv.restrictNormalHom L₂ (phiK * tau) = b
    rw [map_mul, hphi₂, one_mul, htau]

/-- The canonical restriction equivalence for two fields generating their ambient compositum. -/
noncomputable def galoisCompatibleFiberProductEquiv
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [Normal K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) :
    Gal(E/K) ≃*
      groupFiberProduct (restrictToSharedLeft L₁ L₂) (restrictToSharedRight L₁ L₂) :=
  MulEquiv.ofBijective (compatibleRestriction L₁ L₂)
    ⟨compatibleRestriction_injective L₁ L₂ hsup,
      compatibleRestriction_surjective L₁ L₂ hsup⟩

/-- Theorem 96.1: a finite Galois compositum is the compatible restriction fiber product. -/
theorem galois_compatible_fiber_product
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [Normal K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) :
    ∃ equiv :
        Gal(E/K) ≃*
          groupFiberProduct (restrictToSharedLeft L₁ L₂) (restrictToSharedRight L₁ L₂),
      equiv.toMonoidHom = compatibleRestriction L₁ L₂ := by
  exact ⟨galoisCompatibleFiberProductEquiv L₁ L₂ hsup, rfl⟩

#print axioms galois_compatible_fiber_product

-- Field carriers are neither empty nor singletons; Galois groups contain the identity.
example {K E : Type*} [Field K] [Field E] [Algebra K E] :
    Nonempty K ∧ Nontrivial K ∧ Nonempty Gal(E/K) :=
  ⟨⟨0⟩, inferInstance, ⟨1⟩⟩

-- Constant homomorphisms impose no compatibility constraint.
example {G₁ G₂ H : Type*} [Group G₁] [Group G₂] [Group H] :
    groupFiberProduct (1 : G₁ →* H) (1 : G₂ →* H) = ⊤ := by
  ext pair
  simp [groupFiberProduct]

-- The source's `E = K`, encoded as `L₁ ⊓ L₂ = ⊥`, recovers the existing product result.
example {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [IsGalois K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    (∃ fiberEquiv :
        Gal(E/K) ≃*
          groupFiberProduct (restrictToSharedLeft L₁ L₂) (restrictToSharedRight L₁ L₂),
      fiberEquiv.toMonoidHom = compatibleRestriction L₁ L₂) ∧
      ∃ productEquiv : Gal(E/K) ≃* Gal(L₁/K) × Gal(L₂/K),
        productEquiv.toMonoidHom = jointRestriction L₁ L₂ := by
  exact ⟨galois_compatible_fiber_product L₁ L₂ hsup,
    trivial_intersection_galois_product L₁ L₂ hsup hinf⟩

-- `L₁ = L₂`: the fiber product is diagonal.
example {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L : IntermediateField K E) [Normal K L] (sigma : Gal(E/K)) :
    (compatibleRestriction L L sigma).1.1 = (compatibleRestriction L L sigma).1.2 :=
  rfl

-- `L₁ ≤ L₂`: generation forces the larger field to be the whole ambient compositum.
example {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) (hle : L₁ ≤ L₂)
    (hsup : L₁ ⊔ L₂ = ⊤) : L₂ = ⊤ := by
  rw [sup_eq_right.mpr hle] at hsup
  exact hsup

-- Without generation, the ambient-field conclusion can fail injectivity, even over `ℝ ⊆ ℂ`.
example :
    let L₁ : IntermediateField ℝ ℂ := ⊥
    let L₂ : IntermediateField ℝ ℂ := ⊥
    L₁ ⊓ L₂ = ⊥ ∧ ¬Function.Injective (jointRestriction L₁ L₂) :=
  composite_generation_is_necessary

-- There is no numeric depth parameter, so an `n = 0` audit is inapplicable.

end D5.S3.Factorization.Galois.GaloisCompatibleFiberProduct
