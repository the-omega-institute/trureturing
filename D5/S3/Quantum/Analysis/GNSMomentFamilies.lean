/- GID: D5/S3/Quantum/Analysis/GNSMomentFamilies
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/GNSMomentFamilies
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Full continuous moment families in the actual GNS commutant. -/

/-
admission_basis: escape-witness
escape_witness: exists_lift
exists_lift: proof_shape: content; positive domination and the four-positive-part
decomposition construct the range lift on the full complex continuous algebra.
familyEquiv retains both inverse constructions and the prescribed first moment.
The coefficient identities and positivity-faithfulness are consumed by the lift,
its converse and GNSOverlapRigidity.spectral_moments_of_all_overlap_optima.
These are classical GNS and continuous-functional-calculus constructions;
no literature novelty or compressed-centralizer classification is asserted.
-/

import D5.S3.Quantum.Analysis.GNSOrderCoordinates
import D5.S3.Quantum.Analysis.NormalMomentFamily
import D5.S3.Quantum.Analysis.PositiveMomentRigidity

/-! The coefficient map is injective on the actual closed commutant. Positive
moments lift by domination; four positive parts lift every complex moment.
The vector functional is faithful on this commutant even for singular inputs. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace

namespace D5.S3.Quantum.Analysis.GNSMomentFamilies

open GNSOrderCoordinates NormalMomentFamily

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual commutant of the completed GNS representation. -/
def commutant (ψ : A →ₚ[ℂ] ℂ) : StarSubalgebra ℂ (ψ.GNS →L[ℂ] ψ.GNS) :=
  StarSubalgebra.centralizer ℂ (Set.range ψ.gnsStarAlgHom)

instance commutant_closed (ψ : A →ₚ[ℂ] ℂ) :
    IsClosed (commutant ψ : Set (ψ.GNS →L[ℂ] ψ.GNS)) := by
  rw [commutant, StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

instance commutant_cstar (ψ : A →ₚ[ℂ] ℂ) : CStarAlgebra (commutant ψ) :=
  StarSubalgebra.cstarAlgebra (commutant ψ)

instance commutant_starOrderedRing (ψ : A →ₚ[ℂ] ℂ) : StarOrderedRing (commutant ψ) :=
  Subtype.starOrderedRing (𝕜 := ℂ) (commutant ψ)

private theorem mem_commutant (ψ : A →ₚ[ℂ] ℂ) (T : ψ.GNS →L[ℂ] ψ.GNS) :
    T ∈ commutant ψ ↔ ∀ a, Commute T (ψ.gnsStarAlgHom a) := by
  rw [commutant, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h _ ⟨a, rfl⟩).1.symm
  · intro h g hg
    obtain ⟨a, rfl⟩ := hg
    exact ⟨(h a).eq.symm, by simpa only [← map_star] using (h (star a)).eq.symm⟩

private theorem commutes (ψ : A →ₚ[ℂ] ℂ) (T : commutant ψ) :
    ∀ a, Commute T.val (ψ.gnsStarAlgHom a) :=
  (mem_commutant ψ T.val).mp T.property

/-- The genuine continuous coefficient functional, complex-linear in the operator. -/
def coefficientMap (ψ : A →ₚ[ℂ] ℂ) : commutant ψ →ₗ[ℂ] StrongDual ℂ A where
  toFun T := Physicslib4.GNS.coeffFunctional ψ.gnsStarAlgHom (cyclicVector ψ) T.val
  map_add' T S := by
    ext a
    change inner ℂ (cyclicVector ψ) ((T.val + S.val) (ψ.gnsStarAlgHom a (cyclicVector ψ))) = _
    simp only [add_apply, inner_add_right]
    rfl
  map_smul' z T := by
    ext a
    change inner ℂ (cyclicVector ψ) ((z • T.val) (ψ.gnsStarAlgHom a (cyclicVector ψ))) = _
    simp only [smul_apply, inner_smul_right]
    rfl

theorem coefficientMap_injective (ψ : A →ₚ[ℂ] ℂ) :
    Function.Injective (coefficientMap ψ) := by
  intro T S h
  apply Subtype.ext
  exact coefficient_injective ψ T.val S.val (commutes ψ T) (commutes ψ S)
    (congrArg ContinuousLinearMap.toLinearMap h)

theorem coefficientMap_nonneg (ψ : A →ₚ[ℂ] ℂ) (T : commutant ψ) :
    (∀ a, 0 ≤ a → 0 ≤ coefficientMap ψ T a) ↔ 0 ≤ T :=
  coefficient_nonneg_iff ψ T.val (commutes ψ T)

theorem coefficientMap_order (ψ : A →ₚ[ℂ] ℂ) (T S : commutant ψ) :
    (∀ a, 0 ≤ a → coefficientMap ψ T a ≤ coefficientMap ψ S a) ↔ T ≤ S :=
  coefficient_order_iff ψ T.val S.val (commutes ψ T) (commutes ψ S)

theorem coefficientMap_one (ψ : A →ₚ[ℂ] ℂ) :
    (coefficientMap ψ 1).toLinearMap = ψ.toLinearMap := by
  ext a
  change inner ℂ (ψ.toPreGNS 1 : ψ.GNS)
    (ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS 1 : ψ.GNS)) = ψ a
  simp [PositiveLinearMap.leftMulMapPreGNS, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def]

/-- Evaluation at the unnormalized cyclic vector, on the actual commutant. -/
def vectorFunctional (ψ : A →ₚ[ℂ] ℂ) : commutant ψ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((ContinuousLinearMap.apply ℂ ℂ (1 : A)).toLinearMap.comp (coefficientMap ψ))
    (fun T hT => (coefficientMap_nonneg ψ T).mpr hT 1 zero_le_one)

/-- Positivity-faithfulness requires neither faithful inputs nor a normal GNS representation. -/
theorem vectorFunctional_faithful (ψ : A →ₚ[ℂ] ℂ) (T : commutant ψ)
    (hT : 0 ≤ T) (hzero : vectorFunctional ψ T = 0) : T = 0 := by
  apply coefficientMap_injective ψ
  rw [map_zero]
  apply norm_eq_zero.mp
  rw [NormalL1Realization.positive_norm_eq_mass _
    ((coefficientMap_nonneg ψ T).mpr hT)]
  change (vectorFunctional ψ T).re = 0
  rw [hzero, Complex.zero_re]

/-- The GNS input retains both original positive continuous dual functionals. -/
def pairFunctional (ρ σ : StrongDual ℂ A)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a) : A →ₚ[ℂ] ℂ :=
  positiveOfDual (ρ + σ) (fun a ha => add_nonneg (hρ a ha) (hσ a ha))

/-- The original first-moment coordinate, constructed from rho <= rho + sigma. -/
def pairCoordinate (ρ σ : StrongDual ℂ A)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a) :
    commutant (pairFunctional ρ σ hρ hσ) :=
  let ψ := pairFunctional ρ σ hρ hσ
  let hd : Dominated (positiveOfDual ρ hρ) ψ :=
    fun a ha => le_add_of_nonneg_right (hσ a ha)
  ⟨coordinate (positiveOfDual ρ hρ) ψ hd,
    (mem_commutant ψ _).mpr (coordinate_mem _ ψ hd).2.2⟩

theorem pairCoordinate_coefficient (ρ σ : StrongDual ℂ A)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a) :
    coefficientMap (pairFunctional ρ σ hρ hσ) (pairCoordinate ρ σ hρ hσ) = ρ := by
  ext a
  exact (coordinate_represents _ _ _ a).symm

private theorem positive_range (ψ : A →ₚ[ℂ] ℂ)
    (η : StrongDual ℂ A) (hη : ∀ a, 0 ≤ a → 0 ≤ η a)
    (r : ℝ) (hr : 0 < r) (hbound : ∀ a, 0 ≤ a → η a ≤ r • ψ a) :
    η ∈ LinearMap.range (coefficientMap ψ) := by
  let φ : A →ₚ[ℂ] ℂ := positiveOfDual (r⁻¹ • η)
    (fun a ha => smul_nonneg (inv_nonneg.mpr hr.le) (hη a ha))
  have hd : Dominated φ ψ := by
    intro a ha
    have h := smul_le_smul_of_nonneg_left (hbound a ha) (inv_nonneg.mpr hr.le)
    change r⁻¹ • η a ≤ ψ a
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
  let R : commutant ψ := ⟨coordinate φ ψ hd,
    (mem_commutant ψ _).mpr (coordinate_mem φ ψ hd).2.2⟩
  refine ⟨r • R, ?_⟩
  ext a
  change inner ℂ (cyclicVector ψ)
    ((r • coordinate φ ψ hd) (ψ.gnsStarAlgHom a (cyclicVector ψ))) = η a
  rw [smul_apply, ← Complex.coe_smul, inner_smul_right]
  change (r : ℂ) * coefficient ψ (coordinate φ ψ hd) a = η a
  have hrep : coefficient ψ (coordinate φ ψ hd) a = φ a :=
    (coordinate_represents φ ψ hd a).symm
  rw [hrep]
  change r • (r⁻¹ • η a) = η a
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

set_option maxHeartbeats 800000 in
-- Elaborating the actual nested commutant, dual and GNS instances requires this limit.
private theorem moment_range {ρ σ : StrongDual ℂ A}
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (F : Family ρ σ) (g : C(Interval, ℂ)) :
    linearMap F g ∈ LinearMap.range (coefficientMap (pairFunctional ρ σ hρ hσ)) := by
  let ψ := pairFunctional ρ σ hρ hσ
  have hp (f : C(Interval, ℂ)) (hf : 0 ≤ f) :
      linearMap F f ∈ LinearMap.range (coefficientMap ψ) := by
    apply positive_range ψ _ (F.property.2.2.1 f hf) (‖f‖ + 1) (by positivity)
    intro a ha
    have hn : 0 ≤ (‖f‖ + 1 : ℂ) • (1 : C(Interval, ℂ)) - f := by
      intro x
      change (0 : ℂ) ≤ (‖f‖ + 1 : ℂ) * 1 - f x
      apply Complex.nonneg_iff.mpr
      have hi := (Complex.nonneg_iff.mp (hf x)).2
      exact ⟨by simp only [mul_one, Complex.sub_re, Complex.add_re,
                    Complex.one_re, Complex.ofReal_re]; linarith [(Complex.re_le_norm (f x)).trans
                    (f.norm_coe_le_norm x)], by simpa using hi.symm⟩
    have h := F.property.2.2.1 _ hn a ha
    change 0 ≤ linearMap F _ a at h
    rw [map_sub, map_smul, sub_apply, smul_apply, unit_value] at h
    change linearMap F f a ≤ ((‖f‖ + 1 : ℝ) : ℂ) * (ρ + σ) a
    simpa only [sub_nonneg, RingHom.id_apply, smul_eq_mul, Complex.coe_smul,
      Complex.ofReal_add, Complex.ofReal_one] using h
  obtain ⟨f, hf, _, he⟩ := CStarAlgebra.exists_sum_four_nonneg g
  rw [he, map_sum]
  simp_rw [map_smul]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hp (f i) (hf i)))

private abbrev momentApply (ψ : A →ₚ[ℂ] ℂ)
    (Z : C(Interval, ℂ) →ₚ[ℂ] commutant ψ) (g : C(Interval, ℂ)) : commutant ψ := Z g

private abbrev momentCoefficient (ψ : A →ₚ[ℂ] ℂ) (T : commutant ψ) : StrongDual ℂ A :=
  coefficientMap ψ T

set_option maxHeartbeats 800000 in
-- Elaborating the actual nested commutant, dual and GNS instances requires this limit.
/-- Every full Family lifts to a positive complex-linear map into its actual GNS commutant.
The coefficients agree for every complex continuous function, including both prescribed moments. -/
theorem exists_lift {ρ σ : StrongDual ℂ A}
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (F : Family ρ σ) :
    let ψ := pairFunctional ρ σ hρ hσ
    ∃ Z : C(Interval, ℂ) →ₚ[ℂ] commutant ψ,
      momentApply ψ Z 1 = 1 ∧
      (∀ g, momentCoefficient ψ (momentApply ψ Z g) = linearMap F g) ∧
      momentApply ψ Z posterior = pairCoordinate ρ σ hρ hσ := by
  let ψ := pairFunctional ρ σ hρ hσ
  let e := LinearEquiv.ofInjective (coefficientMap ψ) (coefficientMap_injective ψ)
  let L := e.symm.toLinearMap.comp
    ((linearMap F).codRestrict (LinearMap.range (coefficientMap ψ)) (moment_range hρ hσ F))
  have he (g : C(Interval, ℂ)) : coefficientMap ψ (L g) = linearMap F g := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨linearMap F g, moment_range hρ hσ F g⟩)
  let Z : C(Interval, ℂ) →ₚ[ℂ] commutant ψ := PositiveLinearMap.mk₀ L (by
    intro g hg
    apply (coefficientMap_nonneg ψ _).mp
    rw [he]
    exact F.property.2.2.1 g hg)
  refine ⟨Z, ?_, he, ?_⟩
  · apply coefficientMap_injective ψ
    change coefficientMap ψ (L 1) = _
    rw [he, unit_value]
    apply ContinuousLinearMap.coe_injective
    exact (coefficientMap_one ψ).symm
  · apply coefficientMap_injective ψ
    change coefficientMap ψ (L posterior) = _
    rw [he, posterior_value, pairCoordinate_coefficient]

set_option maxHeartbeats 800000 in
-- Elaborating the actual nested commutant, dual and GNS instances requires this limit.
/-- The converse includes the indispensable first-moment condition for the fixed pair. -/
def familyOfMap {ρ σ : StrongDual ℂ A}
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (Z : C(Interval, ℂ) →ₚ[ℂ] commutant (pairFunctional ρ σ hρ hσ))
    (hu : momentApply (pairFunctional ρ σ hρ hσ) Z 1 = 1)
    (hc : momentApply (pairFunctional ρ σ hρ hσ) Z posterior = pairCoordinate ρ σ hρ hσ) :
    Family ρ σ :=
  ofLinearMap ((coefficientMap _).comp Z.toLinearMap)
    (fun g hg => (coefficientMap_nonneg _ _).mpr (Z.map_nonneg hg))
    (by
      change coefficientMap _ (momentApply _ Z 1) = _
      rw [hu]
      apply ContinuousLinearMap.coe_injective
      exact coefficientMap_one _)
    (by change coefficientMap _ (momentApply _ Z posterior) = _
        rw [hc, pairCoordinate_coefficient])

/-- The correspondence retains every complex continuous coordinate in both directions. -/
theorem familyOfMap_agrees {ρ σ : StrongDual ℂ A}
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (Z : C(Interval, ℂ) →ₚ[ℂ] commutant (pairFunctional ρ σ hρ hσ))
    (hu : momentApply (pairFunctional ρ σ hρ hσ) Z 1 = 1)
    (hc : momentApply (pairFunctional ρ σ hρ hσ) Z posterior = pairCoordinate ρ σ hρ hσ)
    (g : C(Interval, ℂ)) :
    linearMap (familyOfMap hρ hσ Z hu hc) g =
      momentCoefficient (pairFunctional ρ σ hρ hσ)
        (momentApply (pairFunctional ρ σ hρ hσ) Z g) := rfl

set_option maxHeartbeats 800000 in
-- Elaborating the actual nested commutant, dual and GNS instances requires this limit.
/-- The full continuous-moment correspondence, with the fixed first moment on the right. -/
def familyEquiv (ρ σ : StrongDual ℂ A)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a) :
    Family ρ σ ≃
      {Z : C(Interval, ℂ) →ₚ[ℂ] commutant (pairFunctional ρ σ hρ hσ) //
        momentApply (pairFunctional ρ σ hρ hσ) Z 1 = 1 ∧
        momentApply (pairFunctional ρ σ hρ hσ) Z posterior = pairCoordinate ρ σ hρ hσ} where
  toFun F := ⟨(exists_lift hρ hσ F).choose,
    (exists_lift hρ hσ F).choose_spec.1, (exists_lift hρ hσ F).choose_spec.2.2⟩
  invFun Z := familyOfMap hρ hσ Z.val Z.property.1 Z.property.2
  left_inv F := by
    apply Subtype.ext
    funext g
    apply DFunLike.ext
    intro a
    change coefficientMap _ ((exists_lift hρ hσ F).choose g) a = linearMap F g a
    exact congrArg (fun η : StrongDual ℂ A => η a)
      ((exists_lift hρ hσ F).choose_spec.2.1 g)
  right_inv Z := by
    apply Subtype.ext
    apply PositiveLinearMap.ext
    intro g
    apply coefficientMap_injective _
    exact ((exists_lift hρ hσ
      (familyOfMap hρ hσ Z.val Z.property.1 Z.property.2)).choose_spec.2.1 g).trans
        (familyOfMap_agrees hρ hσ Z.val Z.property.1 Z.property.2 g)

#print axioms vectorFunctional_faithful
#print axioms exists_lift
#print axioms familyEquiv

end D5.S3.Quantum.Analysis.GNSMomentFamilies
