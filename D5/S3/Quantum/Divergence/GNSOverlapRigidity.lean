/- GID: D5/S3/Quantum/Divergence/GNSOverlapRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/GNSOverlapRigidity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original all-threshold overlap optimality forces full spectral moments. -/

/-
admission_basis: escape-witness
escape_witness: spectral_moments_of_all_overlap_optima
spectral_moments_of_all_overlap_optima: proof_shape: content; the constructed
GNS moment lift supplies the actual commutant map, whose scalar CFC hinge
bounds follow from the original overlap maximum. Hinge rigidity supplies the
full homomorphism, and the original Family supplies the whole complex-L1 map.
All private lemmas are consumed by this theorem. The GNS, CFC and positive-map
ingredients are classical; no centralizer completion is asserted.
-/

import D5.S3.Quantum.Analysis.GNSMomentFamilies
import D5.S3.Quantum.Divergence.NormalOverlapCompatibility

/-! All-threshold optimality is the original scalar overlap hypothesis.
The resulting homomorphism agrees with the full complex moment Family and
has its real overlap images equal to the actual continuous functional calculus.
No compressed-centralizer conclusion is asserted. -/

noncomputable section
open Set MeasureTheory
open scoped ComplexOrder Topology

namespace D5.S3.Quantum.Divergence.GNSOverlapRigidity

open Analysis.GNSMomentFamilies Analysis.GNSOrderCoordinates
open Analysis.NormalMomentFamily Analysis.PositiveMomentRigidity
open Analysis.ConcreteCoefficientSeries Analysis.ConcreteCoefficientPredual
open GeneralConvexReverseTestAttainment NormalOverlapCompatibility

private def realCoordinate : C(Interval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
private def realOverlap (t : ℝ) : C(Interval, ℝ) :=
  ⟨fun x => min (x : ℝ) (t * (1 - x)), by fun_prop⟩
private def realHinge (s : ℝ) : C(Interval, ℝ) :=
  ⟨fun x => max ((x : ℝ) - s) 0, by fun_prop⟩

private theorem overlap_hinge (s : ℝ) (hs : s < 1) :
    realOverlap (s / (1 - s)) =
      realCoordinate - (1 + s / (1 - s)) • realHinge s := by
  ext x
  let t := s / (1 - s)
  have ht : 0 < 1 + t := by
    have he : 1 + t = 1 / (1 - s) := by dsimp [t]; field_simp; ring
    rw [he]
    exact div_pos zero_lt_one (sub_pos.mpr hs)
  have hts : t = (1 + t) * s := by dsimp [t]; field_simp; ring
  change min (x : ℝ) (t * (1 - x)) = (x : ℝ) - (1 + t) * max ((x : ℝ) - s) 0
  rcases le_total (x : ℝ) s with hx | hx
  · rw [max_eq_right (sub_nonpos.mpr hx), min_eq_left (by nlinarith), mul_zero, sub_zero]
  · rw [max_eq_left (sub_nonneg.mpr hx), min_eq_right (by nlinarith)]
    nlinarith

section FunctionalCalculus

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The actual real continuous-functional-calculus overlap operator. -/
def spectralOverlap (C : B) (t : ℝ) : B :=
  cfc (fun x : ℝ => min x (t * (1 - x))) C

omit [PartialOrder B] [StarOrderedRing B] in
private theorem calculus_hinge (C : B) (hC : IsSelfAdjoint C)
    (hspec : spectrum ℝ C ⊆ Icc 0 1) (s : ℝ) :
    cfcHomSuperset hC hspec (realHinge s) = (C - algebraMap ℝ B s)⁺ := by
  have he : cfcHomSuperset hC hspec (realHinge s) =
      cfc (fun x : ℝ => max (x - s) 0) C := by
    rw [cfcHomSuperset_apply, cfc_apply _ C hC (by fun_prop)]
    rfl
  rw [he, CFC.posPart_def, cfcₙ_eq_cfc]
  have hsub : cfc (fun x : ℝ => x - s) C = C - algebraMap ℝ B s := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => s) C (by fun_prop) (by fun_prop)]
    change cfc (id : ℝ → ℝ) C - cfc (fun _ : ℝ => s) C = _
    rw [cfc_id ℝ C hC, cfc_const s C hC]
  rw [← hsub, ← cfc_comp (fun x : ℝ => x⁺) (fun x : ℝ => x - s) C hC]
  rfl

private def realHom (Φ : C(Interval, ℂ) →⋆ₐ[ℂ] B) : C(Interval, ℝ) →⋆ₐ[ℝ] B :=
  { (Φ.toAlgHom.restrictScalars ℝ).comp complexify with
    map_star' := by
      intro g
      change Φ (complexify (star g)) = star (Φ (complexify g))
      rw [← map_star]
      congr 1
      ext x
      change (g x : ℂ) = star (g x : ℂ)
      simp }

private theorem realHom_eq_calculus (Φ : C(Interval, ℂ) →⋆ₐ[ℂ] B)
    (C : B) (hC : IsSelfAdjoint C) (hspec : spectrum ℝ C ⊆ Icc 0 1)
    (hc : Φ coordinate = C) : realHom Φ = cfcHomSuperset hC hspec := by
  apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Icc (0 : ℝ) 1)
    _ _ (by
      change Continuous (fun f => Φ (complexify f))
      exact (map_continuous Φ).comp (Complex.ofRealCLM.compLeftContinuous ℝ Interval).continuous)
    (cfcHomSuperset_continuous hC hspec)
  exact hc.trans (cfcHomSuperset_id hC hspec).symm

omit [StarOrderedRing B] in
private theorem coordinate_bounds (Z : C(Interval, ℂ) →ₚ[ℂ] B) (hu : Z 1 = 1) :
    0 ≤ Z coordinate ∧ Z coordinate ≤ 1 := by
  refine ⟨Z.map_nonneg (fun x => Complex.le_def.mpr ⟨x.2.1, rfl⟩), ?_⟩
  exact (Z.monotone (show coordinate ≤ 1 from
    fun x => Complex.le_def.mpr ⟨x.2.2, rfl⟩)).trans_eq hu

private theorem spectrum_bounds (C : B) (h0 : 0 ≤ C) (h1 : C ≤ 1) :
    spectrum ℝ C ⊆ Icc 0 1 := fun x hx =>
  ⟨spectrum_nonneg_of_nonneg h0 hx, (CFC.le_one_iff C).mp h1 x hx⟩

omit [PartialOrder B] [StarOrderedRing B] in
private theorem real_overlap_calculus (C : B) (hC : IsSelfAdjoint C)
    (hspec : spectrum ℝ C ⊆ Icc 0 1) (t : ℝ) :
    cfcHomSuperset hC hspec (realOverlap t) =
      cfc (fun x : ℝ => min x (t * (1 - x))) C := by
  rw [cfcHomSuperset_apply, cfc_apply _ C hC (by fun_prop)]
  rfl

private theorem overlap_calculus_bounds (C : B) (h0 : 0 ≤ C) (h1 : C ≤ 1)
    (t : ℝ) (ht : 0 < t) :
    let T := cfc (fun x : ℝ => min x (t * (1 - x))) C
    0 ≤ T ∧ T ≤ C ∧ T ≤ (t : ℂ) • (1 - C) := by
  have hspec := spectrum_bounds C h0 h1
  let Q : C(Interval, ℝ) →⋆ₐ[ℝ] B := cfcHomSuperset h0.isSelfAdjoint hspec
  have hQu : Q realCoordinate = C := cfcHomSuperset_id h0.isSelfAdjoint hspec
  have hp : 0 ≤ Q (realOverlap t) := map_nonneg Q (fun x =>
    le_min x.2.1 (mul_nonneg ht.le (sub_nonneg.mpr x.2.2)))
  have hl : Q (realOverlap t) ≤ C :=
    (OrderHomClass.mono Q (show realOverlap t ≤ realCoordinate from
      fun x => min_le_left _ _)).trans_eq hQu
  have hr : Q (realOverlap t) ≤ t • (1 - C) := by
    have h := OrderHomClass.mono Q (show realOverlap t ≤ t • (1 - realCoordinate) from
      fun x => min_le_right _ _)
    simpa only [map_smul, map_sub, map_one, hQu] using h
  have he : Q (realOverlap t) = cfc (fun x : ℝ => min x (t * (1 - x))) C :=
    real_overlap_calculus C h0.isSelfAdjoint hspec t
  simpa only [he, Complex.coe_smul] using And.intro hp (And.intro hl hr)

private theorem spectral_of_overlap_bounds (Z : C(Interval, ℂ) →ₚ[ℂ] B)
    (hunit : Z 1 = 1) (φ : B →ₚ[ℂ] ℂ)
    (hfaithful : ∀ b : B, 0 ≤ b → φ b = 0 → b = 0)
    (hbound : ∀ t : ℝ, 0 < t →
      (φ (cfc (fun x : ℝ => min x (t * (1 - x))) (Z coordinate))).re ≤
        (φ (Z (overlapFunction t))).re) :
    ∃ Φ : C(Interval, ℂ) →⋆ₐ[ℂ] B,
      (∀ g, Φ g = Z g) ∧ Φ coordinate = Z coordinate ∧
      ∀ t : ℝ, Φ (overlapFunction t) =
        cfc (fun x : ℝ => min x (t * (1 - x))) (Z coordinate) := by
  let C := Z coordinate
  obtain ⟨hC0, hC1⟩ := coordinate_bounds Z hunit
  have hspec := spectrum_bounds C hC0 hC1
  let Q : C(Interval, ℝ) →⋆ₐ[ℝ] B := cfcHomSuperset hC0.isSelfAdjoint hspec
  have hQu : Q realCoordinate = C := cfcHomSuperset_id hC0.isSelfAdjoint hspec
  have hhinge (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
      (φ (Z (hinge s))).re ≤ (φ ((Z coordinate - algebraMap ℝ B s)⁺)).re := by
    let t := s / (1 - s)
    have ht : 0 < t := div_pos hs0 (sub_pos.mpr hs1)
    have he := overlap_hinge s hs1
    have hec : overlapFunction t = coordinate - ((1 + t : ℝ) : ℂ) • hinge s := by
      change complexify (realOverlap t) = complexify realCoordinate -
        ((1 + t : ℝ) : ℂ) • complexify (realHinge s)
      rw [he, map_sub, map_smul]
      rfl
    have hb := hbound t ht
    rw [← real_overlap_calculus C hC0.isSelfAdjoint hspec t] at hb
    have hQh : Q (realHinge s) = (C - algebraMap ℝ B s)⁺ :=
      calculus_hinge C hC0.isSelfAdjoint hspec s
    rw [hec, map_sub, map_smul] at hb
    have hQr : Q (realOverlap t) = C - (1 + t) • (C - algebraMap ℝ B s)⁺ := by
      rw [he, map_sub, map_smul, hQu, hQh]
    change (φ (Q (realOverlap t))).re ≤ _ at hb
    rw [hQr, map_sub, map_sub, φ.map_smul_of_tower, map_smul] at hb
    have hb' : (φ C).re - (1 + t) * (φ ((C - algebraMap ℝ B s)⁺)).re ≤
        (φ C).re - (1 + t) * (φ (Z (hinge s))).re := by
      simpa only [Complex.sub_re, smul_eq_mul, RCLike.smul_re, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hb
    change (φ (Z (hinge s))).re ≤ (φ ((C - algebraMap ℝ B s)⁺)).re
    nlinarith
  obtain ⟨_, Φ, hagree, hΦu⟩ := exists_starAlgHom_of_scalar_hinges Z hunit φ hfaithful hhinge
  refine ⟨Φ, hagree, hΦu, ?_⟩
  intro t
  have h := congrArg (fun Q => Q (realOverlap t))
    (realHom_eq_calculus Φ C hC0.isSelfAdjoint hspec hΦu)
  change Φ (overlapFunction t) = cfcHomSuperset hC0.isSelfAdjoint hspec (realOverlap t) at h
  exact h.trans (real_overlap_calculus C hC0.isSelfAdjoint hspec t)

private theorem coefficient_overlap_bounds
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (K : B →ₗ[ℂ] StrongDual ℂ A)
    (hpos : ∀ T, 0 ≤ T → Positive (K T))
    (hmono : ∀ T S, T ≤ S → Below (K T) (K S))
    (C : B) (h0 : 0 ≤ C) (h1 : C ≤ 1) (t : ℝ) (ht : 0 < t) :
    Positive (K (spectralOverlap C t)) ∧
      Below (K (spectralOverlap C t)) (K C) ∧
      Below (K (spectralOverlap C t)) (t • K (1 - C)) := by
  have hOp := overlap_calculus_bounds C h0 h1 t ht
  refine ⟨hpos _ hOp.1, hmono _ _ hOp.2.1, ?_⟩
  have hr := hmono _ _ hOp.2.2
  have he : K ((t : ℂ) • (1 - C)) = t • K (1 - C) := by
    rw [map_smul, Complex.coe_smul]
  intro a ha
  exact (hr a ha).trans_eq (congrArg (fun η : StrongDual ℂ A => η a) he)

end FunctionalCalculus

section CommutantOperations

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private abbrev gnsCarrier (ψ : A →ₚ[ℂ] ℂ) : Type _ := commutant ψ

private abbrev gnsSemiring (ψ : A →ₚ[ℂ] ℂ) : Semiring (gnsCarrier ψ) := inferInstance
attribute [local instance] gnsSemiring

private abbrev gnsAlgebra (ψ : A →ₚ[ℂ] ℂ) : Algebra ℂ (gnsCarrier ψ) := inferInstance
attribute [local instance] gnsAlgebra

private abbrev gnsStar (ψ : A →ₚ[ℂ] ℂ) : Star (gnsCarrier ψ) := inferInstance
attribute [local instance] gnsStar

private abbrev gnsAddCommMonoid (ψ : A →ₚ[ℂ] ℂ) : AddCommMonoid (gnsCarrier ψ) :=
  inferInstance
attribute [local instance] gnsAddCommMonoid

private abbrev gnsModule (ψ : A →ₚ[ℂ] ℂ) : Module ℂ (gnsCarrier ψ) := inferInstance
attribute [local instance] gnsModule

private abbrev gnsTopology (ψ : A →ₚ[ℂ] ℂ) : TopologicalSpace (gnsCarrier ψ) :=
  inferInstance
attribute [local instance] gnsTopology

private abbrev gnsApply (ψ : A →ₚ[ℂ] ℂ)
    (Φ : C(Interval, ℂ) →⋆ₐ[ℂ] gnsCarrier ψ) (g : C(Interval, ℂ)) : gnsCarrier ψ := Φ g

private abbrev gnsCoefficient (ψ : A →ₚ[ℂ] ℂ) (T : gnsCarrier ψ) : StrongDual ℂ A :=
  coefficientMap ψ T

private abbrev gnsVectorValue (ψ : A →ₚ[ℂ] ℂ) (T : gnsCarrier ψ) : ℂ :=
  vectorFunctional ψ T

end CommutantOperations

private theorem vectorFunctional_apply
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ψ : A →ₚ[ℂ] ℂ) (T : gnsCarrier ψ) :
    gnsVectorValue ψ T = gnsCoefficient ψ T 1 := rfl

set_option maxHeartbeats 800000 in
-- The generic family uses both continuous dual and ordered C-star structures.
private theorem spectral_family_data
    {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (K : B →ₗ[ℂ] StrongDual ℂ A)
    (hpos : ∀ T, 0 ≤ T → Positive (K T))
    (hmono : ∀ T S, T ≤ S → Below (K T) (K S))
    (Z : C(Interval, ℂ) →ₚ[ℂ] B) (hunit : Z 1 = 1)
    (hcoeff : ∀ g, K (Z g) = linearMap F g)
    (φ : B →ₚ[ℂ] ℂ) (hφ : ∀ T, φ T = K T 1)
    (hfaithful : ∀ T, 0 ≤ T → φ T = 0 → T = 0)
    (v : ℝ → ℝ)
    (hmax : ∀ t : ℝ, 0 < t → ∀ η : StrongDual ℂ A,
      Positive η → Below η ρ → Below η (t • σ) → (η 1).re ≤ v t)
    (hopt : ∀ t : ℝ, 0 < t → (overlap F t 1).re = v t) :
    ∃ Φ : C(Interval, ℂ) →⋆ₐ[ℂ] B,
      Φ posterior = Z posterior ∧
      (∀ g, K (Φ g) = linearMap F g) ∧
      (∀ t : ℝ, Φ (overlapFunction t) = spectralOverlap (Z coordinate) t) ∧
      (∀ t : ℝ, 0 < t → (φ (spectralOverlap (Z coordinate) t)).re = v t) := by
  let C := Z coordinate
  have hC0 := (coordinate_bounds Z hunit).1
  have hC1 := (coordinate_bounds Z hunit).2
  have hKone : K 1 = ρ + σ :=
    (congrArg K hunit).symm.trans ((hcoeff 1).trans (unit_value F))
  have hKrho : K C = ρ := (hcoeff posterior).trans (posterior_value F)
  have hKsigma : K (1 - C) = σ := by
    rw [map_sub, hKone, hKrho, add_sub_cancel_left]
  have hbound (t : ℝ) (ht : 0 < t) :
      (φ (spectralOverlap C t)).re ≤ (φ (Z (overlapFunction t))).re := by
    let T := spectralOverlap C t
    have hOp := coefficient_overlap_bounds K hpos hmono C hC0 hC1 t ht
    have hηρ : Below (K T) ρ := fun a ha =>
      (hOp.2.1 a ha).trans_eq (congrArg (fun η : StrongDual ℂ A => η a) hKrho)
    have hησ : Below (K T) (t • σ) := fun a ha =>
      (hOp.2.2 a ha).trans_eq (congrArg (fun η : StrongDual ℂ A => (t • η) a) hKsigma)
    have hb := hmax t ht (K T) hOp.1 hηρ hησ
    have hright : (φ (Z (overlapFunction t))).re = (overlap F t 1).re :=
      (congrArg Complex.re (hφ _)).trans
        (congrArg (fun η : StrongDual ℂ A => (η 1).re) (hcoeff _))
    exact (congrArg Complex.re (hφ T)).trans_le
      (hb.trans_eq ((hopt t ht).symm.trans hright.symm))
  obtain ⟨Φ, hagree, _, hover⟩ :=
    spectral_of_overlap_bounds Z hunit φ hfaithful hbound
  have hΦcoeff (g : C(Interval, ℂ)) : K (Φ g) = linearMap F g :=
    (congrArg K (hagree g)).trans (hcoeff g)
  refine ⟨Φ, hagree posterior, hΦcoeff, hover, ?_⟩
  intro t ht
  have he : φ (spectralOverlap C t) = linearMap F (overlapFunction t) 1 :=
    (congrArg φ (hover t).symm).trans
      ((hφ _).trans (congrArg (fun η : StrongDual ℂ A => η 1) (hΦcoeff _)))
  exact (congrArg Complex.re he).trans (hopt t ht)

-- Keep the actual GNS construction behind its proved coefficient interfaces
-- while elaborating applications; unfolding it repeats completion reductions.
attribute [local irreducible] pairFunctional pairCoordinate commutant coefficientMap
  vectorFunctional

section ConcreteCarrier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private abbrev concreteAlgebra (M : VonNeumannAlgebra H) : Type _ := M.toStarSubalgebra

@[instance_reducible]
private def concreteCStar (M : VonNeumannAlgebra H) : CStarAlgebra (concreteAlgebra M) :=
  inferInstance

@[instance_reducible]
private def concreteOrder (M : VonNeumannAlgebra H) : PartialOrder (concreteAlgebra M) :=
  inferInstance

@[instance_reducible]
private def concreteStarOrdered (M : VonNeumannAlgebra H) :
    StarOrderedRing (concreteAlgebra M) := inferInstance

end ConcreteCarrier

attribute [local instance] concreteCStar concreteOrder concreteStarOrdered

private abbrev concreteNonUnitalCStar
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : NonUnitalCStarAlgebra (concreteAlgebra M) := inferInstance

attribute [local instance] concreteNonUnitalCStar

private abbrev concreteTopology
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : TopologicalSpace (concreteAlgebra M) := inferInstance

attribute [local instance] concreteTopology

private abbrev concreteAddCommMonoid
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : AddCommMonoid (concreteAlgebra M) := inferInstance

attribute [local instance] concreteAddCommMonoid

private abbrev concreteModule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : Module ℂ (concreteAlgebra M) := inferInstance

attribute [local instance] concreteModule

set_option maxHeartbeats 3000000 in
-- The concrete GNS and L1 application elaborates several dependent C-star structures.
private theorem spectral_data
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ (concreteAlgebra M))
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
    (F : Family ρ σ)
    (hopt : ∀ t : ℝ, 0 < t → (overlap F t 1).re = overlapValue M ρ σ t) :
    let ψ := pairFunctional ρ σ hρ hσ
    let N : Type _ := gnsCarrier ψ
    letI : CStarAlgebra N := commutant_cstar ψ
    letI : PartialOrder N := inferInstance
    letI : StarOrderedRing N := commutant_starOrderedRing ψ
    let C : N := pairCoordinate ρ σ hρ hσ
    ∃ Φ : C(Interval, ℂ) →⋆ₐ[ℂ] N,
      gnsApply ψ Φ posterior = C ∧
      (∀ g, gnsCoefficient ψ (gnsApply ψ Φ g) = linearMap F g) ∧
      (∀ t : ℝ, gnsApply ψ Φ (overlapFunction t) = spectralOverlap C t) ∧
      (∀ t : ℝ, 0 < t →
        (gnsVectorValue ψ (spectralOverlap C t)).re =
          overlapValue M ρ σ t) := by
  let ψ := pairFunctional ρ σ hρ hσ
  have hlift := exists_lift (A := M.toStarSubalgebra) (ρ := ρ) (σ := σ) hρ hσ F
  rcases hlift with ⟨Z, hunit, hcoeff, hfirst⟩
  have hmax (t : ℝ) (ht : 0 < t) :=
    (value_attained M ρ σ hρ hσ hρs hσs t ht).choose_spec.2
  have hs := spectral_family_data (A := M.toStarSubalgebra) (B := commutant ψ) F
    (coefficientMap ψ) (fun T hT => (coefficientMap_nonneg ψ T).mpr hT)
    (fun T S hTS => (coefficientMap_order ψ T S).mpr hTS)
    Z hunit hcoeff (vectorFunctional ψ) (vectorFunctional_apply ψ)
    (vectorFunctional_faithful ψ) (overlapValue M ρ σ) hmax hopt
  rcases hs with ⟨Φ, hΦfirst, hΦcoeff, hover, hmass⟩
  have hpair (t : ℝ) : Φ (overlapFunction t) =
      spectralOverlap (pairCoordinate ρ σ hρ hσ) t :=
    (hover t).trans (congrArg (fun C => spectralOverlap C t) hfirst)
  refine ⟨Φ, hΦfirst.trans hfirst, hΦcoeff, hpair, ?_⟩
  intro t ht
  have hc : spectralOverlap (pairCoordinate ρ σ hρ hσ) t =
      spectralOverlap (Z coordinate) t :=
    congrArg (fun C => spectralOverlap C t) hfirst.symm
  exact (congrArg (fun T => (vectorFunctional ψ T).re) hc).trans (hmass t ht)

set_option maxHeartbeats 3000000 in
-- The concrete GNS and whole-L1 application retains its dependent carriers.
/-- Original all-threshold overlap optima give all complex spectral moments
and an actual preparation on the entire complex L1 space. -/
theorem spectral_moments_of_all_overlap_optima
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ (concreteAlgebra M))
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
    (F : Family ρ σ)
    (hopt : ∀ t : ℝ, 0 < t → (overlap F t 1).re = overlapValue M ρ σ t) :
    let ψ := pairFunctional ρ σ hρ hσ
    let N : Type _ := gnsCarrier ψ
    letI : CStarAlgebra N := commutant_cstar ψ
    letI : PartialOrder N := inferInstance
    letI : StarOrderedRing N := commutant_starOrderedRing ψ
    let C : N := pairCoordinate ρ σ hρ hσ
    let μ := scalarMeasure F
    letI : IsFiniteMeasure μ := inferInstance
    let V := StrongDual ℂ (concreteAlgebra M)
    letI : NormedAddCommGroup V := inferInstance
    letI : NormedSpace ℂ V := inferInstance
    ∃ Φ : C(Interval, ℂ) →⋆ₐ[ℂ] N,
      gnsApply ψ Φ posterior = C ∧
      (∀ g, gnsCoefficient ψ (gnsApply ψ Φ g) = linearMap F g) ∧
      (∀ t : ℝ, gnsApply ψ Φ (overlapFunction t) = spectralOverlap C t) ∧
      (∀ t : ℝ, 0 < t →
        (gnsVectorValue ψ (spectralOverlap C t)).re =
          overlapValue M ρ σ t) ∧
      ∃ Γ : (Interval →₁[μ] ℂ) →L[ℂ] V,
        (∀ g, Γ (ContinuousMap.toLp 1 μ ℂ g) = gnsCoefficient ψ (gnsApply ψ Φ g)) ∧
        (∀ h, IsCoefficientSeries M (Γ h)) ∧
        (∀ h, Analysis.NormalFunctionals.IsOrderNormal (Γ h)) ∧
        (∀ h, (∀ᵐ x ∂μ, 0 ≤ h x) → Positive (Γ h)) ∧
        (∀ h, Γ h 1 = ∫ x, h x ∂μ) ∧ ‖Γ‖ ≤ 1 ∧
        Γ (ContinuousMap.toLp 1 μ ℂ posterior) = ρ ∧
        Γ (ContinuousMap.toLp 1 μ ℂ (1 - posterior)) = σ := by
  let ψ := pairFunctional ρ σ hρ hσ
  have hspec := spectral_data M ρ σ hρ hσ hρs hσs F hopt
  rcases hspec with ⟨Φ, hfirst, hcoeff, hover, hmass⟩
  refine ⟨Φ, hfirst, hcoeff, hover, hmass, ?_⟩
  have hPrep := standard_posterior_realization M ρ σ hρ hσ hρs hσs F
  rcases hPrep with ⟨Γ, hΓ, hn, hp, hm, hb, hl, hr, hE⟩
  have hs (h) : IsCoefficientSeries M (Γ h) :=
    (mem_coefficientSpace_iff_series M (Γ h)).mp (hE.choose h)
  refine ⟨Γ, ?_, hs, hn, hp, hm, hb, hl, hr⟩
  intro g
  exact (hΓ g).trans (hcoeff g).symm

#print axioms spectral_moments_of_all_overlap_optima

end D5.S3.Quantum.Divergence.GNSOverlapRigidity
