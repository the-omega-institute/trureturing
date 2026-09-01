/- GID: D5/S3/Factorization/Galois/GaloisFusion
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GaloisFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Restriction pairs form a fiber product; disjoint and Frobenius cases are audited. -/
/- Library-search audit trail (2026-08-25):
   * Lean LSP search commands were unavailable; scripted and pinned-source searches were used.
   * Exact hits include `IntermediateField.LinearDisjoint.iff_inf_eq_bot`,
     `IntermediateField.LinearDisjoint.of_inf_eq_bot`, `AlgEquiv.restrictNormalHom_surjective`,
     and `IntermediateField.restrictRestrictAlgEquivMapHom_surjective`.
   * `IntermediateField.fixingSubgroup_sup` proves injectivity from generation by both fields.
   * No packaged product equivalence or intersection fiber-product restriction theorem was found.
   * No theorem relates separately chosen `arithFrobAt` values across intermediate extensions.
     The result therefore maps the existing conjugacy-class observer through restriction homs.
   * `NumberField.exists_not_isUnramifiedAt_int` supplies the concrete ramified-prime audit. -/

import D5.S3.Factorization.Galois.GaloisPrimeObserver
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.ExistsRamified

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.GaloisFusion

open D5.S3.Factorization.Galois.GaloisPrimeObserver

/-- The group fiber product of two homomorphisms with a common target. -/
def groupFiberProduct {G₁ G₂ H : Type*} [Group G₁] [Group G₂] [Group H]
    (left : G₁ →* H) (right : G₂ →* H) : Subgroup (G₁ × G₂) where
  carrier := {pair | left pair.1 = right pair.2}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change left (a * b).1 = right (a * b).2
    simpa only [Prod.fst_mul, Prod.snd_mul, map_mul] using congrArg₂ (· * ·) ha hb
  inv_mem' := by
    intro a ha
    change left a⁻¹.1 = right a⁻¹.2
    simpa only [Prod.fst_inv, Prod.snd_inv, map_inv] using congrArg Inv.inv ha

/-- The common intersection field carrying the shared restriction constraint. -/
def sharedField {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) : IntermediateField K E :=
  L₁ ⊓ L₂

/-- Restriction from the left Galois group to the shared intersection field. -/
noncomputable def restrictToSharedLeft
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂] :
    Gal(L₁/K) →* Gal(sharedField L₁ L₂/K) := by
  let S : IntermediateField K E := sharedField L₁ L₂
  let hS : S ≤ L₁ := by
    dsimp [S, sharedField]
    exact inf_le_left
  let T : IntermediateField K L₁ := S.restrict hS
  letI : Normal K S := by
    change Normal K (L₁ ⊓ L₂ : IntermediateField K E)
    infer_instance
  letI : Normal K T := Normal.of_algEquiv (S.restrict_algEquiv hS)
  exact (AlgEquiv.autCongr (S.restrict_algEquiv hS)).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom T)

/-- Restriction from the right Galois group to the shared intersection field. -/
noncomputable def restrictToSharedRight
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂] :
    Gal(L₂/K) →* Gal(sharedField L₁ L₂/K) := by
  let S : IntermediateField K E := sharedField L₁ L₂
  let hS : S ≤ L₂ := by
    dsimp [S, sharedField]
    exact inf_le_right
  let T : IntermediateField K L₂ := S.restrict hS
  letI : Normal K S := by
    change Normal K (L₁ ⊓ L₂ : IntermediateField K E)
    infer_instance
  letI : Normal K T := Normal.of_algEquiv (S.restrict_algEquiv hS)
  exact (AlgEquiv.autCongr (S.restrict_algEquiv hS)).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom T)

/-- The joint restriction to both observer fields. -/
noncomputable def jointRestriction
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂] :
    Gal(E/K) →* Gal(L₁/K) × Gal(L₂/K) :=
  MonoidHom.prod (AlgEquiv.restrictNormalHom L₁) (AlgEquiv.restrictNormalHom L₂)

private theorem restrictNormalHom_bot_eq_one
    {K E : Type*} [Field K] [Field E] [Algebra K E] (sigma : Gal(E/K)) :
    AlgEquiv.restrictNormalHom (⊥ : IntermediateField K E) sigma = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp x.property
  simp only [AlgEquiv.restrictNormalHom_apply]
  change sigma (x : E) = x
  rw [← hr]
  exact sigma.commutes r

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

private theorem restrictToSharedRight_apply
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    (sigma : Gal(L₂/K)) (x : sharedField L₁ L₂) :
    ((restrictToSharedRight L₁ L₂ sigma x : sharedField L₁ L₂) : E) =
      ((sigma ⟨x, x.property.2⟩ : L₂) : E) := by
  let S : IntermediateField K E := sharedField L₁ L₂
  let hS : S ≤ L₂ := by
    dsimp [S, sharedField]
    exact inf_le_right
  let T : IntermediateField K L₂ := S.restrict hS
  letI : Normal K S := by
    change Normal K (L₁ ⊓ L₂ : IntermediateField K E)
    infer_instance
  letI : Normal K T := Normal.of_algEquiv (S.restrict_algEquiv hS)
  let equiv : S ≃ₐ[K] T := S.restrict_algEquiv hS
  let y : T := (AlgEquiv.restrictNormalHom T sigma) (equiv x)
  change ((equiv.symm y : S) : E) = ((sigma ⟨x, x.property.2⟩ : L₂) : E)
  have htransport : ((equiv.symm y : S) : E) = ((y : T) : L₂) := by
    exact congrArg (fun z : T => ((z : L₂) : E)) (equiv.apply_symm_apply y)
  have hrestrict : ((y : T) : L₂) = sigma ((equiv x : T) : L₂) := by
    exact AlgEquiv.restrictNormal_commutes sigma T (equiv x)
  have hrestrictE : ((y : T) : L₂) = ((sigma ((equiv x : T) : L₂) : L₂) : E) :=
    congrArg (fun z : L₂ => ((z : L₂) : E)) hrestrict
  exact htransport.trans (hrestrictE.trans rfl)

/-- Corollary 96.1: every joint restriction satisfies the shared-field constraint. -/
theorem joint_restriction_lands_in_fiber_product
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    (sigma : Gal(E/K)) :
    jointRestriction L₁ L₂ sigma ∈
      groupFiberProduct (restrictToSharedLeft L₁ L₂) (restrictToSharedRight L₁ L₂) := by
  change restrictToSharedLeft L₁ L₂ (AlgEquiv.restrictNormalHom L₁ sigma) =
    restrictToSharedRight L₁ L₂ (AlgEquiv.restrictNormalHom L₂ sigma)
  ext x
  rw [restrictToSharedLeft_apply, restrictToSharedRight_apply]
  simp [AlgEquiv.restrictNormalHom_apply]

#print axioms joint_restriction_lands_in_fiber_product

/-- For finite Galois subextensions, trivial intersection is exactly linear disjointness. -/
theorem linearDisjoint_iff_trivial_intersection
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [FiniteDimensional K L₁] [FiniteDimensional K L₂] :
    L₁.LinearDisjoint L₂ ↔ L₁ ⊓ L₂ = ⊥ :=
  IntermediateField.LinearDisjoint.iff_inf_eq_bot

#print axioms linearDisjoint_iff_trivial_intersection

private theorem jointRestriction_injective
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) : Function.Injective (jointRestriction L₁ L₂) := by
  intro sigma tau hst
  have h₁ : ∀ y : L₁, sigma y = tau y := by
    intro y
    simpa [jointRestriction, AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Prod.fst hst) y)
  have h₂ : ∀ y : L₂, sigma y = tau y := by
    intro y
    simpa [jointRestriction, AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Prod.snd hst) y)
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

private theorem jointRestriction_surjective
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [IsGalois K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    Function.Surjective (jointRestriction L₁ L₂) := by
  have hdisjoint : L₁.LinearDisjoint L₂ :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hrank : Module.finrank L₂ E = Module.finrank K L₁ :=
    hdisjoint.finrank_right_eq_finrank hsup
  letI : FiniteDimensional L₂ E :=
    FiniteDimensional.of_finrank_pos (hrank.trans_gt Module.finrank_pos)
  letI : IsGalois L₂ E := IsGalois.sup_right L₁ L₂ hsup
  letI : Normal K (⊤ : IntermediateField K E) :=
    hsup ▸ (inferInstance : Normal K (L₁ ⊔ L₂ : IntermediateField K E))
  letI : Normal K E := Normal.of_algEquiv IntermediateField.topEquiv
  rintro ⟨a, b⟩
  obtain ⟨tau, htau⟩ := AlgEquiv.restrictNormalHom_surjective E b
  let delta : Gal(L₁/K) := a * (AlgEquiv.restrictNormalHom L₁ tau)⁻¹
  obtain ⟨phi, hphi⟩ :=
    IntermediateField.restrictRestrictAlgEquivMapHom_surjective L₁ L₂ hinf delta
  let phiK : Gal(E/K) := MulSemiringAction.toAlgAut Gal(E/L₂) K E phi
  refine ⟨phiK * tau, ?_⟩
  apply Prod.ext
  · change AlgEquiv.restrictNormalHom L₁ (phiK * tau) = a
    rw [map_mul]
    change IntermediateField.restrictRestrictAlgEquivMapHom K L₁ L₂ E phi *
      AlgEquiv.restrictNormalHom L₁ tau = a
    rw [hphi]
    simp [delta]
  · change AlgEquiv.restrictNormalHom L₂ (phiK * tau) = b
    rw [map_mul, htau]
    have hfix : AlgEquiv.restrictNormalHom L₂ phiK = 1 := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      simpa [phiK, AlgEquiv.restrictNormalHom_apply] using phi.commutes x
    rw [hfix, one_mul]

/-- The canonical restriction equivalence when the two fields generate and meet trivially. -/
noncomputable def trivialIntersectionRestrictionEquiv
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [IsGalois K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    Gal(E/K) ≃* Gal(L₁/K) × Gal(L₂/K) :=
  MulEquiv.ofBijective (jointRestriction L₁ L₂)
    ⟨jointRestriction_injective L₁ L₂ hsup,
      jointRestriction_surjective L₁ L₂ hsup hinf⟩

/-- Corollary 96.2: trivial intersection gives the product via joint restriction. -/
theorem trivial_intersection_galois_product
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L₁ L₂ : IntermediateField K E)
    [IsGalois K L₁] [IsGalois K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    ∃ equiv : Gal(E/K) ≃* Gal(L₁/K) × Gal(L₂/K),
      equiv.toMonoidHom = jointRestriction L₁ L₂ := by
  exact ⟨trivialIntersectionRestrictionEquiv L₁ L₂ hsup hinf, rfl⟩

#print axioms trivial_intersection_galois_product

/-- Two names for the same nontrivial extension give a diagonal, nonsurjective observation. -/
theorem differently_named_extensions_not_independent :
    let L₁ : IntermediateField ℝ ℂ := ⊤
    let L₂ : IntermediateField ℝ ℂ := ⊤
    sharedField L₁ L₂ ≠ ⊥ ∧
      ¬Function.Surjective
        (MonoidHom.prod (MonoidHom.id Gal(ℂ/ℝ)) (MonoidHom.id Gal(ℂ/ℝ))) := by
  dsimp only
  constructor
  · simp only [sharedField, inf_idem]
    intro htop
    have hI : Complex.I ∈ (⊥ : IntermediateField ℝ ℂ) := by
      rw [← htop]
      exact IntermediateField.mem_top
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hI
    have him := congrArg Complex.im hr
    norm_num at him
  · intro hsurjective
    obtain ⟨sigma, hsigma⟩ := hsurjective (1, Complex.conjAe)
    have hleft := congrArg Prod.fst hsigma
    have hright := congrArg Prod.snd hsigma
    have hconj : (1 : Gal(ℂ/ℝ)) = Complex.conjAe := hleft.symm.trans hright
    have hI := DFunLike.congr_fun hconj Complex.I
    have him := congrArg Complex.im hI
    norm_num at him

#print axioms differently_named_extensions_not_independent

/-- Without generation of the ambient field, trivial intersection need not give injectivity. -/
theorem composite_generation_is_necessary :
    let L₁ : IntermediateField ℝ ℂ := ⊥
    let L₂ : IntermediateField ℝ ℂ := ⊥
    L₁ ⊓ L₂ = ⊥ ∧ ¬Function.Injective (jointRestriction L₁ L₂) := by
  dsimp only
  constructor
  · simp
  · intro hinjective
    have hpair :
        jointRestriction (⊥ : IntermediateField ℝ ℂ) ⊥ 1 =
          jointRestriction (⊥ : IntermediateField ℝ ℂ) ⊥ Complex.conjAe := by
      apply Prod.ext <;>
        simp [jointRestriction, restrictNormalHom_bot_eq_one]
    have hone : (1 : Gal(ℂ/ℝ)) = Complex.conjAe := hinjective hpair
    have hI := DFunLike.congr_fun hone Complex.I
    have him := congrArg Complex.im hI
    norm_num at him

#print axioms composite_generation_is_necessary

/-- The two restrictions of Mathlib's chosen composite Frobenius element. -/
noncomputable def frobeniusRestrictionPair
    {K E R S : Type*} [Field K] [Field E] [Algebra K E]
    [CommRing R] [CommRing S] [Algebra R S]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    [MulSemiringAction Gal(E/K) S] [SMulCommClass Gal(E/K) R S]
    [Finite Gal(E/K)] [Algebra.IsInvariant R S Gal(E/K)]
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : Gal(L₁/K) × Gal(L₂/K) :=
  jointRestriction L₁ L₂ (arithFrobAt R Gal(E/K) Q)

/-- Corollary 96.3: the unramified Frobenius output restricts to a compatible pair. -/
theorem frobenius_fusion_compatible
    {K E R S : Type*} [Field K] [Field E] [Algebra K E]
    [CommRing R] [CommRing S] [Algebra R S]
    (L₁ L₂ : IntermediateField K E) [Normal K L₁] [Normal K L₂]
    [MulSemiringAction Gal(E/K) S] [SMulCommClass Gal(E/K) R S]
    [Finite Gal(E/K)] [Algebra.IsInvariant R S Gal(E/K)]
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] :
    mathlibFrobeniusAt (R := R) (G := Gal(E/K)) Q =
        some (ConjClasses.mk (arithFrobAt R Gal(E/K) Q)) ∧
      Option.map (ConjClasses.map (AlgEquiv.restrictNormalHom L₁))
          (mathlibFrobeniusAt (R := R) (G := Gal(E/K)) Q) =
        some (ConjClasses.mk (frobeniusRestrictionPair (R := R) L₁ L₂ Q).1) ∧
      Option.map (ConjClasses.map (AlgEquiv.restrictNormalHom L₂))
          (mathlibFrobeniusAt (R := R) (G := Gal(E/K)) Q) =
        some (ConjClasses.mk (frobeniusRestrictionPair (R := R) L₁ L₂ Q).2) ∧
      frobeniusRestrictionPair (R := R) L₁ L₂ Q ∈
        groupFiberProduct (restrictToSharedLeft L₁ L₂) (restrictToSharedRight L₁ L₂) := by
  have htag : mathlibFrobeniusAt (R := R) (G := Gal(E/K)) Q =
      some (ConjClasses.mk (arithFrobAt R Gal(E/K) Q)) := by
    have hunramified : Algebra.IsUnramifiedAt R Q := inferInstance
    simp [mathlibFrobeniusAt, hunramified]
  refine ⟨htag, ?_, ?_, ?_⟩
  · rw [htag]
    rfl
  · rw [htag]
    rfl
  · exact joint_restriction_lands_in_fiber_product L₁ L₂ _

#print axioms frobenius_fusion_compatible

/-- The reused observer has no Frobenius class on its ramified branch. -/
theorem ramified_frobenius_is_none
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G]
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (hramified : ¬Algebra.IsUnramifiedAt R Q) :
    mathlibFrobeniusAt (R := R) (G := G) Q = none := by
  simp [mathlibFrobeniusAt, hramified]

#print axioms ramified_frobenius_is_none

/-- The third cyclotomic field has a concrete ramified prime, so unramifiedness is necessary. -/
theorem ramification_hypothesis_is_necessary :
    ∃ (P : Ideal (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) (_ : P.IsMaximal),
      Finite (NumberField.RingOfIntegers (CyclotomicField 3 ℚ) ⧸ P) ∧
        ¬Algebra.IsUnramifiedAt ℤ P := by
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hdegree : Module.finrank ℚ (CyclotomicField 3 ℚ) ≠ 1 := by
    rw [IsCyclotomicExtension.finrank (n := 3) (CyclotomicField 3 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  obtain ⟨P, hP, hramified⟩ := NumberField.exists_not_isUnramifiedAt_int
    (K := CyclotomicField 3 ℚ)
    (𝒪 := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) hdegree
  refine ⟨P, hP, ?_, hramified⟩
  letI : P.IsMaximal := hP
  exact Ring.HasFiniteQuotients.finiteQuotient
    (P.bot_lt_of_maximal
      (NumberField.RingOfIntegers.not_isField (CyclotomicField 3 ℚ))).ne'

#print axioms ramification_hypothesis_is_necessary

-- Empty-carrier audit: fields and Galois groups contain zero and one, respectively.
example {K E : Type*} [Field K] [Field E] [Algebra K E] :
    Nonempty K ∧ Nonempty Gal(E/K) :=
  ⟨⟨0⟩, ⟨1⟩⟩

-- `L₁ = K`: restriction to the bottom intermediate field is the trivial homomorphism.
example {K E : Type*} [Field K] [Field E] [Algebra K E] (sigma : Gal(E/K)) :
    AlgEquiv.restrictNormalHom (⊥ : IntermediateField K E) sigma = 1 :=
  restrictNormalHom_bot_eq_one sigma

-- `L₁ = L₂`: the joint restriction lies on the diagonal.
example {K E : Type*} [Field K] [Field E] [Algebra K E] (L : IntermediateField K E)
    [Normal K L] (sigma : Gal(E/K)) :
    (jointRestriction L L sigma).1 = (jointRestriction L L sigma).2 :=
  rfl

-- `L₁ = L₂ = K`: the intersection is trivial and every self-automorphism is identity.
example {K : Type*} [Field K] :
    (⊤ : IntermediateField K K) ⊓ ⊤ = ⊥ ∧ Subsingleton Gal(K/K) := by
  constructor
  · apply le_antisymm
    · intro x _
      exact IntermediateField.mem_bot.mpr ⟨x, by simp⟩
    · exact bot_le
  · constructor
    intro sigma tau
    ext x
    exact (sigma.commutes x).trans (tau.commutes x).symm

-- There is no numeric depth parameter in these declarations, so an `n = 0` audit is inapplicable.

end D5.S3.Factorization.Galois.GaloisFusion
