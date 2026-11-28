/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qFiniteModularTrace
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Modular trace identities force twisted labels on the electric stabilizer. -/

import D5.S3.FiniteGroups.CosetActions.EtalePermutationTrace
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHolomorphicExtensionObstruction
import Mathlib.Data.Matrix.Mul
import OmegaBuild.Commands

/-!
Dong–Ren–Xu, *On Orbifold Theory*, [arXiv:1507.03306v2](https://arxiv.org/abs/1507.03306v2),
Sections 2.2 and 3, give the modular trace and fixed-point module context.
Here the common finite label space, modular coefficient identities, twisted
support and identification of the paired twining coefficients with the
electric algebra trace enter as hypotheses.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped Matrix
open FiniteGroups.CosetActions.EtalePermutationTrace
  (exists_coset_trace_eq_fixedPoints_and_ne_zero)

local notation "coeffs(" b ")" => (fun i => ((b i : ℕ) : ℂ))

/-- On the subgroup supplied by the finite étale trace theorem, modular
covariance forces a twisted label with positive extension multiplicity. -/
theorem exists_coset_trace_and_positive_twisted_multiplicity
    {G A I : Type*} [Group G] [Finite G] [Fintype I]
    [CommRing A] [Nontrivial A] [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z)
    (b : I → ℕ) (S : Matrix I I ℂ)
    (hInvariant : coeffs(b) ᵥ* S = coeffs(b))
    (u v : G → I → ℂ) (c : G → ℂˣ) (twisted : G → Set I)
    (hCovariance : ∀ g, S *ᵥ u g = (c g : ℂ) • v g)
    (hTrace : ∀ g, coeffs(b) ⬝ᵥ u g = LinearMap.trace ℂ A (ρ g).toLinearMap)
    (hSupport : ∀ g i, i ∉ twisted g → v g i = 0) :
    ∃ K : Subgroup G, ∀ g : G,
      LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ) ∧
      (g ∈ K → ∃ i ∈ twisted g, 0 < b i) := by
  obtain ⟨K, hCoset⟩ := exists_coset_trace_eq_fixedPoints_and_ne_zero ρ hfixed
  refine ⟨K, fun g => ⟨(hCoset g).1, ?_⟩⟩
  intro hg
  have hTransport :
      (c g : ℂ) • (coeffs(b) ⬝ᵥ v g) = LinearMap.trace ℂ A (ρ g).toLinearMap := by
    rw [← dotProduct_smul, ← hCovariance g, Matrix.dotProduct_mulVec, hInvariant, hTrace g]
  have hPair : coeffs(b) ⬝ᵥ v g ≠ 0 := by
    intro hZero
    exact (hCoset g).2 hg (by simpa only [hZero, smul_zero] using hTransport.symm)
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPair
  have hv : v g i ≠ 0 := right_ne_zero_of_mul hi
  have hb : b i ≠ 0 := fun h => hi (by simp [h])
  have hiTwisted : i ∈ twisted g := by
    by_contra hNotTwisted
    exact hv (hSupport g i hNotTwisted)
  exact ⟨i, hiTwisted, Nat.pos_of_ne_zero hb⟩

open ExtremalC48 (SL47)
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open DiagonalCharacterConjugacy (PreservesModes)
open P48qFiniteActionObstruction (p48q_finite_action_obstruction)
open P48qHolomorphicExtensionObstruction (CubicSectorRealization)
open P48qOrderThreeSpectrumTransport (conformalZeroMode)
open P48qTwistedChargeAction (lattice)

universe w x

/-- With a grading-compatible realization of each occupied cubic label in
an integrally graded target, the electric stabilizer has two independent
fixed weight-two states in the P48q lattice carrier. -/
theorem p48q_fixed_quadratics_of_finite_modular_trace
    {G A I : Type*} [Group G] [Finite G] [Fintype I]
    [CommRing A] [Nontrivial A] [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z)
    (b : I → ℕ) (S : Matrix I I ℂ)
    (hInvariant : coeffs(b) ᵥ* S = coeffs(b))
    (u v : G → I → ℂ) (c : G → ℂˣ) (twisted : G → Set I)
    (hCovariance : ∀ g, S *ᵥ u g = (c g : ℂ) • v g)
    (hTrace : ∀ g, coeffs(b) ⬝ᵥ u g = LinearMap.trace ℂ A (ρ g).toLinearMap)
    (hSupport : ∀ g i, i ∉ twisted g → v g i = 0)
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ s : Additive SL47, ∀ a b,
      bilinear lattice (realization s a) (realization s b) = bilinear lattice a b)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    (U : G →* (Carrier lattice ≃ₗ[ℂ] Carrier lattice))
    (hU : Function.Injective U) (hMode : ∀ g, PreservesModes lattice (U g))
    (hOmega : ∀ g, U g (omega lattice (actualInverse lattice)) =
      omega lattice (actualInverse lattice))
    {W : Type x} [AddCommGroup W] [Module ℂ W] (L_W : Module.End ℂ W)
    (hGraded : (⨆ n : ℤ, L_W.eigenspace (n : ℂ)) = ⊤)
    (hRealizeCubic : ∀ g, orderOf g = 3 → ∀ i ∈ twisted g, 0 < b i →
      Nonempty (CubicSectorRealization.{w, x} (U g) L_W)) :
    ∃ K : Subgroup G,
      (∀ g : G,
        LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ)) ∧
      ∃ q : Fin 2 → Carrier lattice, (∀ i, q i ∈ grade lattice 2) ∧
        (∀ k : K, ∀ i, U k (q i) = q i) ∧ LinearIndependent ℂ q := by
  obtain ⟨K, hCoset⟩ := exists_coset_trace_and_positive_twisted_multiplicity
    ρ hfixed b S hInvariant u v c twisted hCovariance hTrace hSupport
  refine ⟨K, fun g => (hCoset g).1, ?_⟩
  obtain ⟨_, _, _, hDichotomy⟩ :=
    p48q_finite_action_obstruction.{w} realization hFaithful hIsometry hExhaustive
      (U.comp K.subtype) (hU.comp Subtype.val_injective) (fun k => hMode k) (fun k => hOmega k)
  rcases hDichotomy with hQuadratics | ⟨k, hOrder, _, hSpectrum⟩
  · exact hQuadratics
  · have hOrderG : orderOf (k : G) = 3 :=
      (orderOf_injective K.subtype Subtype.val_injective k).trans hOrder
    obtain ⟨i, hi, hb⟩ := (hCoset k).2 k.property
    obtain ⟨sector⟩ := hRealizeCubic k hOrderG i hi hb
    let _ := sector.spaceAdd
    let _ := sector.spaceModule
    let L : Module.End ℂ sector.branch :=
      LinearMap.restrict (conformalZeroMode sector.field) sector.stable
    have hNoEigenvalue (n : ℤ) : ¬ L.HasEigenvalue (n : ℂ) := by
      intro hEigenvalue
      obtain ⟨y, hy⟩ := hEigenvalue.exists_hasEigenvector
      have hyNe : (y : sector.space) ≠ 0 := fun h =>
        (Module.End.hasEigenvector_iff.mp hy).2 (Subtype.ext h)
      have hyEigen : conformalZeroMode sector.field (y : sector.space) =
          (n : ℂ) • (y : sector.space) := by
        simpa only [L, LinearMap.coe_restrict_apply, Submodule.coe_smul] using
          congrArg (fun z : sector.branch => (z : sector.space)) hy.apply_eq_smul
      exact (hSpectrum sector.space sector.field sector.fieldLaw sector.lower sector.lowerBound
        sector.finiteWeight (n : ℂ) y hyNe hyEigen).2.2 n rfl
    have hVanish := Omega.LinearAlgebra.eq_zero_of_injective_intertwiner_of_no_eigenvalue
      L L_W (fun n : ℤ => (n : ℂ)) hGraded hNoEigenvalue
      sector.inclusion sector.injective sector.intertwines
    obtain ⟨y, hy, hyNe⟩ := Submodule.exists_mem_ne_zero_of_ne_bot sector.nonzero
    exact (hyNe (congrArg (fun z : sector.branch => (z : sector.space)) (hVanish ⟨y, hy⟩))).elim

#print axioms exists_coset_trace_and_positive_twisted_multiplicity
#print axioms p48q_fixed_quadratics_of_finite_modular_trace

end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion
