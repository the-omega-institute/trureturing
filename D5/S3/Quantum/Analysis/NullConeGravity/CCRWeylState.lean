/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRWeylState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abstract Weyl relations, normalized GNS states and countable vector folium transport. -/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Normed.Operator.Extend
import D5.S3.QuantumStates.GNSExpectation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder InnerProductSpace CStarAlgebra
open UniformSpace.Completion

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState

variable {S A : Type*} [AddCommGroup S] [Module ℝ S]
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ}

/-- Weyl generators for an alternating real form, with norm-dense complex linear span. -/
structure WeylSystem (σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) where
  alternating : ∀ f, σ f f = 0
  weyl : S → A
  weyl_zero : weyl 0 = 1
  weyl_mul : ∀ f g, weyl f * weyl g =
    Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) • weyl (f + g)
  weyl_star : ∀ f, star (weyl f) = weyl (-f)
  dense_span : Dense (Submodule.span ℂ (Set.range weyl) : Set A)

/-- A normalized state with Gaussian characteristic function of covariance μ. -/
def IsGaussian (W : WeylSystem (A := A) σ)
    (μ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (ω : A →ₚ[ℂ] ℂ) : Prop :=
  ω 1 = 1 ∧ ∀ f : S, ω (W.weyl f) = Complex.exp (-(μ f f : ℂ) / 2)

/-- A state in the countable vector folium of the reference GNS representation.
The vectors absorb the square roots of the mixture weights. -/
def Excitability (ωTarget ωRef : A →ₚ[ℂ] ℂ) : Prop :=
  ∃ ψ : ℕ → ωRef.GNS,
    HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ) ∧
    ∀ a : A, HasSum (fun n => ⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ) (ωTarget a)

/-- The canonical cyclic vector of the completed GNS representation. -/
def gnsVacuum (ω : A →ₚ[ℂ] ℂ) : ω.GNS := (ω.toPreGNS 1 : ω.GNS)

omit [PartialOrder A] [StarOrderedRing A] in
theorem weyl_neg (W : WeylSystem (A := A) σ) (f : S) :
    W.weyl (-f) = star (W.weyl f) := (W.weyl_star f).symm

omit [PartialOrder A] [StarOrderedRing A] in
theorem weyl_unitary (W : WeylSystem (A := A) σ) (f : S) :
    star (W.weyl f) * W.weyl f = 1 ∧ W.weyl f * star (W.weyl f) = 1 := by
  rw [← weyl_neg, W.weyl_mul, W.weyl_mul]
  simp [W.alternating, W.weyl_zero]

omit [PartialOrder A] [StarOrderedRing A] in
theorem weyl_norm_le_one (W : WeylSystem (A := A) σ) (f : S) :
    ‖W.weyl f‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := W.weyl f)
  rw [(weyl_unitary W f).1] at h
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (W.weyl f) 0, norm_zero]
    exact zero_le_one
  · rw [CStarRing.norm_one] at h
    nlinarith [norm_nonneg (W.weyl f)]

theorem gnsVacuum_norm (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1) : ‖gnsVacuum ω‖ = 1 := by
  rw [gnsVacuum, norm_coe]
  have h := D5.S3.QuantumStates.GNSExpectation.expectation_eq_preGNS_norm_sq ω 1
  rw [star_one, one_mul, hω] at h
  have hr := congrArg Complex.re h
  simp only [Complex.one_re, Complex.ofReal_re] at hr
  nlinarith [norm_nonneg (ω.toPreGNS 1)]

theorem gnsVacuum_expectation (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVacuum ω, ω.gnsStarAlgHom a (gnsVacuum ω)⟫_ℂ = ω a := by
  change inner ℂ (ω.toPreGNS 1 : ω.GNS)
    (ω.gnsNonUnitalStarAlgHom a (ω.toPreGNS 1 : ω.GNS)) = ω a
  simp [PositiveLinearMap.leftMulMapPreGNS, PositiveLinearMap.preGNS_inner_def]

private theorem coeff_norm_le (ω : A →ₚ[ℂ] ℂ) (a : A) (x : ω.GNS) :
    ‖⟪x, ω.gnsStarAlgHom a x⟫_ℂ‖ ≤ ‖a‖ * ‖x‖ ^ 2 := calc
  _ ≤ ‖x‖ * ‖ω.gnsStarAlgHom a x‖ := norm_inner_le_norm _ _
  _ ≤ ‖x‖ * (‖ω.gnsStarAlgHom a‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left ((ω.gnsStarAlgHom a).le_opNorm x) (norm_nonneg _)
  _ ≤ ‖x‖ * (‖a‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ω.gnsStarAlgHom a) (norm_nonneg _))
      (norm_nonneg _)
  _ = _ := by ring

theorem state_norm_le (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1) (a : A) :
    ‖ω a‖ ≤ ‖a‖ := by
  simpa only [gnsVacuum_expectation, gnsVacuum_norm ω hω, one_pow, mul_one] using coeff_norm_le ω a (gnsVacuum ω)

theorem state_continuous (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1) : Continuous ω := by
  exact (ω.toLinearMap.mkContinuous 1 (by simpa using state_norm_le ω hω)).continuous

omit [PartialOrder A] [StarOrderedRing A] in
/-- Agreement on the Weyl generators determines a continuous functional. -/
theorem weyl_determines (W : WeylSystem (A := A) σ) (F G : A →L[ℂ] ℂ)
    (h : ∀ f, F (W.weyl f) = G (W.weyl f)) : F = G := by
  ext a
  have hsub : (Submodule.span ℂ (Set.range W.weyl) : Set A) ⊆ {a | F a = G a} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨f, rfl⟩ := hx; exact h f
    | zero => simp
    | add x y _ _ hx hy =>
      change F x = G x at hx
      change F y = G y at hy
      simp [map_add, hx, hy]
    | smul c x _ hx =>
      change F x = G x at hx
      simp [map_smul, hx]
  have hc : closure (Submodule.span ℂ (Set.range W.weyl) : Set A) ⊆ {a | F a = G a} :=
    closure_minimal hsub (isClosed_eq F.continuous G.continuous)
  rw [W.dense_span.closure_eq] at hc
  exact hc (Set.mem_univ a)

/-- A Gaussian covariance determines the positive state uniquely. -/
theorem gaussian_unique (W : WeylSystem (A := A) σ) (μ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (ω₁ ω₂ : A →ₚ[ℂ] ℂ) (h₁ : IsGaussian W μ ω₁) (h₂ : IsGaussian W μ ω₂) :
    ω₁ = ω₂ := by
  let F : A →L[ℂ] ℂ := ⟨ω₁.toLinearMap, state_continuous ω₁ h₁.1⟩
  let G : A →L[ℂ] ℂ := ⟨ω₂.toLinearMap, state_continuous ω₂ h₂.1⟩
  have hFG := weyl_determines W F G (fun f => (h₁.2 f).trans (h₂.2 f).symm)
  ext a
  exact congrArg (fun g : A →L[ℂ] ℂ => g a) hFG

theorem folium_summable (ωRef : A →ₚ[ℂ] ℂ) (ψ : ℕ → ωRef.GNS)
    (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ)) (a : A) :
    Summable (fun n => ⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ) :=
  Summable.of_norm_bounded (hψ.summable.mul_left ‖a‖)
    (fun n => coeff_norm_le ωRef a (ψ n))

theorem folium_norm_le (ωRef : A →ₚ[ℂ] ℂ) (ψ : ℕ → ωRef.GNS)
    (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ)) (a : A) :
    ‖∑' n, ⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ‖ ≤ ‖a‖ := by
  have hb := hψ.summable.mul_left ‖a‖
  have hs : Summable (fun n => ‖⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => coeff_norm_le ωRef a (ψ n)) hb
  calc
    _ ≤ ∑' n, ‖⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ‖a‖ * ‖ψ n‖ ^ 2 := hs.tsum_le_tsum (fun n => coeff_norm_le ωRef a (ψ n)) hb
    _ = ‖a‖ := by rw [tsum_mul_left, hψ.tsum_eq, mul_one]

/-- The vector series gives a continuous linear functional on the whole algebra. -/
def foliumFunctional (ωRef : A →ₚ[ℂ] ℂ) (ψ : ℕ → ωRef.GNS)
    (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ)) : A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' n, ⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ
      map_add' := fun a b => by
        simp only [map_add, add_apply, inner_add_right]
        exact (folium_summable ωRef ψ hψ a).tsum_add (folium_summable ωRef ψ hψ b)
      map_smul' := fun c a => by
        simp only [map_smul, smul_apply, inner_smul_right,
          RingHom.id_apply, smul_eq_mul, tsum_mul_left] }
    1 (by simpa using folium_norm_le ωRef ψ hψ)

theorem excitability_of_weyl_coefficients (W : WeylSystem (A := A) σ)
    (ωTarget ωRef : A →ₚ[ℂ] ℂ) (ψ : ℕ → ωRef.GNS)
    (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ))
    (h : ∀ f, (∑' n, ⟪ψ n, ωRef.gnsStarAlgHom (W.weyl f) (ψ n)⟫_ℂ) = ωTarget (W.weyl f)) :
    Excitability ωTarget ωRef := by
  let F := foliumFunctional ωRef ψ hψ
  let G : A →L[ℂ] ℂ := ⟨ωTarget.toLinearMap, map_continuous ωTarget⟩
  have hFG : F = G := weyl_determines W F G h
  refine ⟨ψ, hψ, fun a => ?_⟩
  have he : F a = G a := congrArg (fun g : A →L[ℂ] ℂ => g a) hFG
  change (∑' n, ⟪ψ n, ωRef.gnsStarAlgHom a (ψ n)⟫_ℂ) = ωTarget a at he
  rw [← he]
  exact (folium_summable ωRef ψ hψ a).hasSum

theorem excitability_of_unitary_intertwining (W : WeylSystem (A := A) σ)
    (ωTarget ωRef : A →ₚ[ℂ] ℂ)
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : ωRef.GNS ≃ₗᵢ[ℂ] K) (π : S → K →L[ℂ] K)
    (hU : ∀ f x, U (ωRef.gnsStarAlgHom (W.weyl f) x) = π f (U x))
    (ψ : ℕ → K) (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ))
    (h : ∀ f, (∑' n, ⟪ψ n, π f (ψ n)⟫_ℂ) = ωTarget (W.weyl f)) :
    Excitability ωTarget ωRef := by
  apply excitability_of_weyl_coefficients W ωTarget ωRef (fun n => U.symm (ψ n))
  · simpa using hψ
  · intro f
    convert h f using 1
    apply tsum_congr
    intro n
    rw [← U.inner_map_map, hU, U.apply_symm_apply]

theorem excitability_refl (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1) : Excitability ω ω := by
  let ψ : ℕ → ω.GNS := fun n => if n = 0 then gnsVacuum ω else 0
  refine ⟨ψ, ?_, fun a => ?_⟩
  · have hs := hasSum_single (f := fun n => ‖ψ n‖ ^ 2) 0
      (fun n hn => by simp [ψ, hn])
    simpa [ψ, gnsVacuum_norm ω hω] using hs
  · have hs := hasSum_single
      (f := fun n => ⟪ψ n, ω.gnsStarAlgHom a (ψ n)⟫_ℂ) 0
      (fun n hn => by simp [ψ, hn])
    simpa only [ψ, ite_true, gnsVacuum_expectation] using hs

section Pullback

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Pullback of a positive linear functional along a unital star homomorphism. -/
private abbrev pullback (ω : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B) : A →ₚ[ℂ] ℂ :=
  ω.comp (PositiveLinearMap.ofClass Φ)

private def prePullback (ω : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B) :
    (pullback ω Φ).PreGNS →ₗᵢ[ℂ] ω.PreGNS where
  toLinearMap := ω.toPreGNS.toLinearMap.comp (Φ.toLinearMap.comp (pullback ω Φ).ofPreGNS.toLinearMap)
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    apply Complex.ofReal_injective
    push_cast
    rw [ω.preGNS_norm_sq, (pullback ω Φ).preGNS_norm_sq]
    change ω (star (Φ ((pullback ω Φ).ofPreGNS x)) * Φ ((pullback ω Φ).ofPreGNS x)) =
      ω (Φ (star ((pullback ω Φ).ofPreGNS x) * (pullback ω Φ).ofPreGNS x))
    rw [map_mul Φ, map_star Φ]

private def gnsPullback (ω : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B) :
    (pullback ω Φ).GNS →ₗᵢ[ℂ] ω.GNS :=
  ((toComplₗᵢ : ω.PreGNS →ₗᵢ[ℂ] ω.GNS).comp (prePullback ω Φ)).fromCompletion

private theorem gnsPullback_coe (ω : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B) (a : A) :
    gnsPullback ω Φ ((pullback ω Φ).toPreGNS a : (pullback ω Φ).GNS) =
      (ω.toPreGNS (Φ a) : ω.GNS) := by
  rw [gnsPullback, LinearIsometry.fromCompletion_apply_coe]
  rfl

private theorem gnsPullback_surjective (ω : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B)
    (hΦ : Function.Surjective Φ) : Function.Surjective (gnsPullback ω Φ) := by
  have hd : DenseRange (fun b : B => (ω.toPreGNS b : ω.GNS)) :=
    UniformSpace.Completion.denseRange_coe.comp ω.toPreGNS.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  have hc := (gnsPullback ω Φ).isometry.isClosedEmbedding.isClosed_range
  have hr : Set.range (fun b : B => (ω.toPreGNS b : ω.GNS)) ⊆ Set.range (gnsPullback ω Φ) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hΦ b
    exact ⟨((pullback ω Φ).toPreGNS a : (pullback ω Φ).GNS), gnsPullback_coe ω Φ a⟩
  have he := closure_minimal hr hc
  rw [hd.closure_range] at he
  exact fun b => he (Set.mem_univ b)

private theorem gnsPullback_intertwines (ω : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B)
    (a : A) (x : (pullback ω Φ).GNS) :
    gnsPullback ω Φ ((pullback ω Φ).gnsStarAlgHom a x) =
      ω.gnsStarAlgHom (Φ a) (gnsPullback ω Φ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    obtain ⟨b, rfl⟩ := (pullback ω Φ).toPreGNS.surjective x
    change gnsPullback ω Φ ((pullback ω Φ).gnsNonUnitalStarAlgHom a
      ((pullback ω Φ).toPreGNS b : (pullback ω Φ).GNS)) = _
    rw [show ω.gnsStarAlgHom (Φ a) = ω.gnsNonUnitalStarAlgHom (Φ a) from rfl]
    simp [gnsPullback_coe, PositiveLinearMap.leftMulMapPreGNS, map_mul]

/-- A quotient of unital C-star algebras pulls folium membership back to the domain,
using the induced surjective isometry between the two GNS completions. -/
theorem excitability_pullback (ωTarget ωRef : B →ₚ[ℂ] ℂ) (Φ : A →⋆ₐ[ℂ] B)
    (hΦ : Function.Surjective Φ) (h : Excitability ωTarget ωRef) :
    Excitability (ωTarget.comp (PositiveLinearMap.ofClass Φ))
      (ωRef.comp (PositiveLinearMap.ofClass Φ)) := by
  obtain ⟨ψ, hψ, hcoeff⟩ := h
  let U := LinearIsometryEquiv.ofSurjective (gnsPullback ωRef Φ) (gnsPullback_surjective ωRef Φ hΦ)
  refine ⟨fun n => U.symm (ψ n), ?_, fun a => ?_⟩
  · simpa using hψ
  · change HasSum (fun n => ⟪U.symm (ψ n),
      (pullback ωRef Φ).gnsStarAlgHom a (U.symm (ψ n))⟫_ℂ) (ωTarget (Φ a))
    have he (n : ℕ) : ⟪U.symm (ψ n), (pullback ωRef Φ).gnsStarAlgHom a (U.symm (ψ n))⟫_ℂ =
        ⟪ψ n, ωRef.gnsStarAlgHom (Φ a) (ψ n)⟫_ℂ := by
      rw [← U.inner_map_map, U.apply_symm_apply]
      have hU (x : (pullback ωRef Φ).GNS) :
          U ((pullback ωRef Φ).gnsStarAlgHom a x) = ωRef.gnsStarAlgHom (Φ a) (U x) :=
        gnsPullback_intertwines ωRef Φ a x
      rw [hU, U.apply_symm_apply]
    simpa only [he] using hcoeff (Φ a)

end Pullback

end D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
