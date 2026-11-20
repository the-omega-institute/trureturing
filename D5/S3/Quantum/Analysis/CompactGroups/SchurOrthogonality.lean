/- GID: D5/S3/Quantum/Analysis/CompactGroups/SchurOrthogonality
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactGroups/SchurOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schur orthogonality of matrix coefficients of irreducible unitary representations. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schur orthogonality of matrix coefficients on compact groups

Let `G` be a compact topological group with a left Haar measure `μ`, and let `ρ`, `σ` be
continuous irreducible representations of `G` on finite-dimensional complex inner product spaces.

* If `σ` acts by isometries and `ρ`, `σ` are not equivalent, then
  `∫ g, ⟪v, ρ g v'⟫ * conj ⟪w, σ g w'⟫ ∂μ = 0`.
* If `ρ` acts by isometries and `μ` is a probability measure, then
  `∫ g, ⟪v, ρ g v'⟫ * conj ⟪w, ρ g w'⟫ ∂μ = ⟪v, w⟫ * ⟪w', v'⟫ / dim V`.

For fixed `v'`, `w'` the map `T x = ∫ g, ⟪w', σ g⁻¹ x⟫ • ρ g v' ∂μ` is linear and, by left
invariance of `μ`, intertwines `σ` with `ρ`. When `σ` acts by isometries,
`conj ⟪w, σ g w'⟫ = ⟪w', σ g⁻¹ w⟫`, so the integral of the product of coefficients is
`⟪v, T w⟫`. Schur's lemma makes `T` zero for inequivalent representations and a scalar `c` for
`σ = ρ`; computing the trace of `T` in an orthonormal basis gives `dim V * c = ⟪w', v'⟫`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- For a representation by isometries, the conjugate of a matrix coefficient is the coefficient
at the inverse with the two vectors exchanged. -/
private lemma conj_inner_apply (σ : Representation ℂ G W) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (g : G) (w w' : W) : conj ⟪w, σ g w'⟫_ℂ = ⟪w', σ g⁻¹ w⟫_ℂ := by
  rw [inner_conj_symm]
  calc ⟪σ g w', w⟫_ℂ = ⟪σ g w', σ g (σ g⁻¹ w)⟫_ℂ := by rw [Representation.self_inv_apply]
    _ = ⟪w', σ g⁻¹ w⟫_ℂ := (⟨σ g, hσ g⟩ : W →ₗᵢ[ℂ] W).inner_map_map _ _

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The integrand `g ↦ ⟪w', σ g⁻¹ x⟫ • ρ g v'` is continuous on the compact group, hence
integrable for the Haar measure. -/
private lemma integrable_smul (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρc : ∀ v, Continuous fun g => ρ g v) (hσc : ∀ w, Continuous fun g => σ g w)
    (v' : V) (w' x : W) :
    Integrable (fun g => ⟪w', σ g⁻¹ x⟫_ℂ • ρ g v') μ :=
  ((continuous_const.inner ((hσc x).comp continuous_inv)).smul
    (hρc v')).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The average `x ↦ ∫ g, ⟪w', σ g⁻¹ x⟫ • ρ g v' ∂μ` is an intertwining map from `σ` to `ρ`. -/
private lemma exists_intertwiningMap [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρc : ∀ v, Continuous fun g => ρ g v)
    (hσc : ∀ w, Continuous fun g => σ g w) (v' : V) (w' : W) :
    ∃ T : Representation.IntertwiningMap σ ρ,
      ∀ x, T x = ∫ g, ⟪w', σ g⁻¹ x⟫_ℂ • ρ g v' ∂μ := by
  let L : W →ₗ[ℂ] V :=
    { toFun := fun x => ∫ g, ⟪w', σ g⁻¹ x⟫_ℂ • ρ g v' ∂μ
      map_add' := fun x y => by
        simp only [map_add, inner_add_right, add_smul]
        exact integral_add (integrable_smul μ ρ σ hρc hσc v' w' x)
          (integrable_smul μ ρ σ hρc hσc v' w' y)
      map_smul' := fun c x => by
        simp only [map_smul, inner_smul_right, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  refine ⟨L.intertwiningMap_of_isIntertwiningMap σ ρ fun h x => ?_, fun x => rfl⟩
  show ∫ g, ⟪w', σ g⁻¹ (σ h x)⟫_ℂ • ρ g v' ∂μ = ρ h (∫ g, ⟪w', σ g⁻¹ x⟫_ℂ • ρ g v' ∂μ)
  calc ∫ g, ⟪w', σ g⁻¹ (σ h x)⟫_ℂ • ρ g v' ∂μ
      = ∫ g, ⟪w', σ (h * g)⁻¹ (σ h x)⟫_ℂ • ρ (h * g) v' ∂μ :=
        (integral_mul_left_eq_self (fun g => ⟪w', σ g⁻¹ (σ h x)⟫_ℂ • ρ g v') h).symm
    _ = ∫ g, LinearMap.toContinuousLinearMap (ρ h) (⟪w', σ g⁻¹ x⟫_ℂ • ρ g v') ∂μ := by
        congr 1
        funext g
        rw [LinearMap.coe_toContinuousLinearMap', map_smul, mul_inv_rev, map_mul, map_mul,
          Module.End.mul_apply, Module.End.mul_apply, Representation.inv_self_apply]
    _ = ρ h (∫ g, ⟪w', σ g⁻¹ x⟫_ℂ • ρ g v' ∂μ) :=
        ContinuousLinearMap.integral_comp_comm _ (integrable_smul μ ρ σ hρc hσc v' w' x)

/-- Schur orthogonality for inequivalent representations: a matrix coefficient of `ρ` is
orthogonal in `L²(μ)` to every matrix coefficient of `σ`. -/
theorem integral_coeff_mul_conj_coeff_eq_zero [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible]
    (hne : IsEmpty (ρ.Equiv σ)) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (hρc : ∀ v, Continuous fun g => ρ g v) (hσc : ∀ w, Continuous fun g => σ g w)
    (v v' : V) (w w' : W) :
    ∫ g, ⟪v, ρ g v'⟫_ℂ * conj ⟪w, σ g w'⟫_ℂ ∂μ = 0 := by
  have : IsEmpty (σ.Equiv ρ) := ⟨fun e => hne.false e.symm⟩
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨T, hT⟩ := exists_intertwiningMap μ ρ σ hρc hσc v' w'
  have hT0 : T = 0 := Subsingleton.elim _ _
  calc ∫ g, ⟪v, ρ g v'⟫_ℂ * conj ⟪w, σ g w'⟫_ℂ ∂μ
      = ∫ g, ⟪v, ⟪w', σ g⁻¹ w⟫_ℂ • ρ g v'⟫_ℂ ∂μ := by
        congr 1
        funext g
        rw [conj_inner_apply σ hσ, inner_smul_right, mul_comm]
    _ = ⟪v, T w⟫_ℂ := by rw [hT, integral_inner (integrable_smul μ ρ σ hρc hσc v' w' w)]
    _ = 0 := by rw [hT0, Representation.IntertwiningMap.coe_zero, Pi.zero_apply, inner_zero_right]

/-- Schur orthogonality for one representation: for the Haar probability measure,
`∫ g, ⟪v, ρ g v'⟫ * conj ⟪w, ρ g w'⟫ ∂μ = ⟪v, w⟫ * ⟪w', v'⟫ / dim V`. -/
theorem integral_coeff_mul_conj_coeff_self [FiniteDimensional ℂ V] [IsProbabilityMeasure μ]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hρc : ∀ v, Continuous fun g => ρ g v) (v v' w w' : V) :
    ∫ g, ⟪v, ρ g v'⟫_ℂ * conj ⟪w, ρ g w'⟫_ℂ ∂μ =
      ⟪v, w⟫_ℂ * ⟪w', v'⟫_ℂ / Module.finrank ℂ V := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨T, hT⟩ := exists_intertwiningMap μ ρ ρ hρc hρc v' w'
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 T
  have hTc : ∀ x, T x = c • x := fun x => by
    rw [← hc, Representation.IntertwiningMap.algebraMap_apply]
    rfl
  have hlin : T.toLinearMap = c • LinearMap.id := LinearMap.ext fun x => hTc x
  set b := stdOrthonormalBasis ℂ V
  have htr : (Module.finrank ℂ V : ℂ) * c = ⟪w', v'⟫_ℂ := by
    calc (Module.finrank ℂ V : ℂ) * c = LinearMap.trace ℂ V T.toLinearMap := by
          rw [hlin, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
      _ = ∑ i, ⟪b i, T (b i)⟫_ℂ := LinearMap.trace_eq_sum_inner _ b
      _ = ∑ i, ∫ g, ⟪b i, ⟪w', ρ g⁻¹ (b i)⟫_ℂ • ρ g v'⟫_ℂ ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hT, integral_inner (integrable_smul μ ρ ρ hρc hρc v' w' (b i))]
      _ = ∫ g, ∑ i, ⟪b i, ⟪w', ρ g⁻¹ (b i)⟫_ℂ • ρ g v'⟫_ℂ ∂μ :=
          (integral_finsetSum _ fun i _ =>
            (integrable_smul μ ρ ρ hρc hρc v' w' (b i)).const_inner (b i)).symm
      _ = ∫ _g, ⟪w', v'⟫_ℂ ∂μ := by
          congr 1
          funext g
          calc ∑ i, ⟪b i, ⟪w', ρ g⁻¹ (b i)⟫_ℂ • ρ g v'⟫_ℂ
              = ⟪w', ρ g⁻¹ (∑ i, ⟪b i, ρ g v'⟫_ℂ • b i)⟫_ℂ := by
                rw [map_sum, inner_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [inner_smul_right, map_smul, inner_smul_right, mul_comm]
            _ = ⟪w', v'⟫_ℂ := by rw [b.sum_repr', Representation.inv_self_apply]
      _ = ⟪w', v'⟫_ℂ := by simp
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  calc ∫ g, ⟪v, ρ g v'⟫_ℂ * conj ⟪w, ρ g w'⟫_ℂ ∂μ
      = ∫ g, ⟪v, ⟪w', ρ g⁻¹ w⟫_ℂ • ρ g v'⟫_ℂ ∂μ := by
        congr 1
        funext g
        rw [conj_inner_apply ρ hρ, inner_smul_right, mul_comm]
    _ = ⟪v, T w⟫_ℂ := by rw [hT, integral_inner (integrable_smul μ ρ ρ hρc hρc v' w' w)]
    _ = ⟪v, w⟫_ℂ * ⟪w', v'⟫_ℂ / Module.finrank ℂ V := by
        rw [hTc, inner_smul_right, ← htr]
        field_simp

end D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
