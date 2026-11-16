/- GID: D5/S3/Quantum/Analysis/GNSSpectralMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/GNSSpectralMoments
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute]
   utility: none
   digest: Genuine complex spectral moment families for prescribed GNS coordinates. -/

import D5.S3.Quantum.Analysis.GNSOrderCoordinates
import D5.S3.Quantum.Analysis.NormalMomentFamily
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! The spectral map is constructed from the complex continuous functional
calculus. Its posterior is the prescribed operator, including endpoint and
zero-space cases. No positive-map lifting theorem is assumed. -/

noncomputable section
open Set
open scoped ComplexOrder InnerProductSpace

namespace D5.S3.Quantum.Analysis.GNSSpectralMoments

open GNSOrderCoordinates NormalMomentFamily

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual commutant of the represented algebra, as a von Neumann algebra. -/
def commutant (ψ : A →ₚ[ℂ] ℂ) : VonNeumannAlgebra ψ.GNS where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ ψ.gnsStarAlgHom.range
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer _)) = Set.centralizer _
    exact Set.centralizer_centralizer_centralizer _

theorem mem_commutant (ψ : A →ₚ[ℂ] ℂ) (T : ψ.GNS →L[ℂ] ψ.GNS) :
    T ∈ commutant ψ ↔ ∀ a, Commute T (ψ.gnsStarAlgHom a) := by
  change T ∈ StarSubalgebra.centralizer ℂ ψ.gnsStarAlgHom.range ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h _ ⟨a, rfl⟩).1.symm
  · intro h g hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨(h a).eq.symm, ?_⟩
    change star (ψ.gnsStarAlgHom a) * T = T * star (ψ.gnsStarAlgHom a)
    rw [← map_star]
    exact (h (star a)).eq.symm

section Spectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem spectrum_re_bounds (C : H →L[ℂ] H) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (z : ℂ) (hz : z ∈ spectrum ℂ C) : z.re ∈ Icc (0 : ℝ) 1 := by
  have hr : z.re ∈ spectrum ℝ C :=
    (IsSelfAdjoint.of_nonneg hC0).spectrumRestricts.subset_preimage hz
  exact ⟨spectrum_nonneg_of_nonneg hC0 hr,
    (CFC.le_one_iff (R := ℝ) C (IsSelfAdjoint.of_nonneg hC0)).mp hC1 _ hr⟩

private def spectrumCoordinate (C : H →L[ℂ] H) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    C(spectrum ℂ C, Interval) where
  toFun z := ⟨z.val.re, spectrum_re_bounds C hC0 hC1 z.val z.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_re.comp continuous_subtype_val

/-- Full complex continuous spectral calculus on the closed posterior interval. -/
def spectralHom (C : H →L[ℂ] H) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    C(Interval, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (cfcHom (IsSelfAdjoint.of_nonneg hC0).isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (spectrumCoordinate C hC0 hC1))

theorem spectralHom_posterior (C : H →L[ℂ] H) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    spectralHom C hC0 hC1 posterior = C := by
  change cfcHom _ _ = C
  refine Eq.trans ?_ (cfcHom_id (R := ℂ) (IsSelfAdjoint.of_nonneg hC0).isStarNormal)
  congr 1
  ext z
  exact (IsSelfAdjoint.of_nonneg hC0).spectrumRestricts.rightInvOn z.property

/-- Real continuous functions agree with the actual real CFC, not a substitute map. -/
theorem spectralHom_real (C : H →L[ℂ] H) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (f : ℝ → ℝ) (hf : Continuous f) :
    spectralHom C hC0 hC1 ⟨fun x => (f x.val : ℂ), by fun_prop⟩ = cfc f C := by
  rw [cfc_real_eq_complex f (IsSelfAdjoint.of_nonneg hC0),
    cfc_apply _ C (IsSelfAdjoint.of_nonneg hC0).isStarNormal (by fun_prop)]
  rfl

theorem spectralHom_commutes (C : H →L[ℂ] H) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (T : H →L[ℂ] H) (hT : Commute C T)
    (g : C(Interval, ℂ)) : Commute (spectralHom C hC0 hC1 g) T :=
  IsSelfAdjoint.commute_cfcHom (IsSelfAdjoint.of_nonneg hC0).isStarNormal
    (IsSelfAdjoint.of_nonneg hC0) hT _

end Spectral

/-- Continuous coefficients of the constructed spectral calculus. -/
def momentMap (ψ : A →ₚ[ℂ] ℂ) (C : ψ.GNS →L[ℂ] ψ.GNS)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) : C(Interval, ℂ) →ₗ[ℂ] StrongDual ℂ A where
  toFun g := Physicslib4.GNS.coeffFunctional ψ.gnsStarAlgHom (cyclicVector ψ)
    (spectralHom C hC0 hC1 g)
  map_add' g h := by
    ext a
    simp [Physicslib4.GNS.coeffFunctional_apply, inner_add_right]
  map_smul' z g := by
    ext a
    simp [Physicslib4.GNS.coeffFunctional_apply, inner_smul_right]

/-- The original pair's spectral family, with both prescribed moments derived. -/
def spectralFamily (ρ σ : StrongDual ℂ A) (ψ : A →ₚ[ℂ] ℂ)
    (C : ψ.GNS →L[ℂ] ψ.GNS) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hc : ∀ a, Commute C (ψ.gnsStarAlgHom a))
    (hρ : coefficient ψ C = ρ.toLinearMap)
    (hσ : coefficient ψ (1 - C) = σ.toLinearMap) : Family ρ σ :=
  ofLinearMap (momentMap ψ C hC0 hC1)
    (by
      intro g hg a ha
      apply (coefficient_nonneg_iff ψ _ (fun a =>
        spectralHom_commutes C hC0 hC1 _ (hc a) g)).mpr ?_ a ha
      obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (show 0 ≤ g from hg)
      rw [map_mul, map_star]
      exact star_mul_self_nonneg _)
    (by
      ext a
      have hr := congrArg (fun f : A →ₗ[ℂ] ℂ => f a) hρ
      have hs := congrArg (fun f : A →ₗ[ℂ] ℂ => f a) hσ
      change inner ℂ (cyclicVector ψ) (spectralHom C hC0 hC1 1
        (ψ.gnsStarAlgHom a (cyclicVector ψ))) = _
      rw [map_one]
      change inner ℂ (cyclicVector ψ) (ψ.gnsStarAlgHom a (cyclicVector ψ)) = ρ a + σ a
      change inner ℂ (cyclicVector ψ) (C (ψ.gnsStarAlgHom a (cyclicVector ψ))) = ρ a at hr
      change inner ℂ (cyclicVector ψ) ((1 - C) (ψ.gnsStarAlgHom a (cyclicVector ψ))) = σ a at hs
      rw [sub_apply, one_apply_eq_self, inner_sub_right, hr] at hs
      linear_combination hs)
    (by
      ext a
      change coefficient ψ (spectralHom C hC0 hC1 posterior) a = ρ a
      rw [spectralHom_posterior, hρ]
      rfl)

theorem spectralFamily_moment (ρ σ : StrongDual ℂ A) (ψ : A →ₚ[ℂ] ℂ)
    (C : ψ.GNS →L[ℂ] ψ.GNS) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hc : ∀ a, Commute C (ψ.gnsStarAlgHom a))
    (hρ : coefficient ψ C = ρ.toLinearMap)
    (hσ : coefficient ψ (1 - C) = σ.toLinearMap)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (linearMap (spectralFamily ρ σ ψ C hC0 hC1 hc hρ hσ)
      ⟨fun x => (f x.val : ℂ), by fun_prop⟩).toLinearMap = coefficient ψ (cfc f C) := by
  change coefficient ψ (spectralHom C hC0 hC1 _) = _
  rw [spectralHom_real C hC0 hC1 f hf]

#print axioms spectralHom_posterior
#print axioms spectralHom_real
#print axioms spectralFamily
#print axioms spectralFamily_moment

end D5.S3.Quantum.Analysis.GNSSpectralMoments
