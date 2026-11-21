/- GID: D5/S3/Quantum/Analysis/CompactGroups/SchurOrthogonality
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactGroups/SchurOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schur orthogonality of matrix coefficients for a finite left-invariant measure on a compact group. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schur orthogonality of matrix coefficients on compact groups

Let `G` be a compact topological group with a finite left-invariant measure `μ`, let `ρ` be a
continuous irreducible representation of `G` on a finite-dimensional complex normed space `V`, and
let `σ` be an irreducible representation of `G` on a complex vector space `W`. For linear
functionals `φ` on `V` and `ψ` on `W` such that every coefficient `g ↦ ψ (σ g w)` is continuous,
`v : V` and `w : W`:

* if `ρ` and `σ` are not equivalent, then `∫ g, φ (ρ g v) * ψ (σ g⁻¹ w) ∂μ = 0`;
* for linear functionals `φ`, `ψ` on `V`,
  `∫ g, φ (ρ g v) * ψ (ρ g⁻¹ w) ∂μ = μ(G) * (φ w * ψ v) / dim V`.

For fixed `v` and `ψ` the map `T x = ∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ` is linear and, by left
invariance of `μ`, intertwines `σ` with `ρ`; applying `φ` to `T w` gives the integral. Schur's
lemma makes `T` zero for inequivalent representations and a scalar `c` for `σ = ρ`. In a basis
`b` of `V`, the trace of `T` is the integral of `∑ i, b.coord i (ψ (ρ g⁻¹ (b i)) • ρ g v)`,
which is `ψ (ρ g⁻¹ (ρ g v)) = ψ v`; hence `dim V * c = μ(G) * ψ v`.
-/

open MeasureTheory

namespace D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality

variable {G V W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasure μ]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

omit [IsTopologicalGroup G] [FiniteDimensional ℂ V] [μ.IsMulLeftInvariant] in
/-- A continuous scalar function times a continuous orbit `g ↦ ρ g v` is integrable on the
compact group. -/
private lemma integrable_smul (ρ : Representation ℂ G V) (hρc : ∀ v, Continuous fun g => ρ g v)
    {f : G → ℂ} (hf : Continuous f) (v : V) : Integrable (fun g => f g • ρ g v) μ :=
  (hf.smul (hρc v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The average `x ↦ ∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ` of continuous coefficients is an intertwining
map from `σ` to `ρ`. -/
private lemma exists_intertwiningMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρc : ∀ v, Continuous fun g => ρ g v) (ψ : W →ₗ[ℂ] ℂ)
    (hψ : ∀ x, Continuous fun g => ψ (σ g⁻¹ x)) (v : V) :
    ∃ T : Representation.IntertwiningMap σ ρ,
      ∀ x, T x = ∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ := by
  have hint : ∀ x, Integrable (fun g => ψ (σ g⁻¹ x) • ρ g v) μ := fun x =>
    integrable_smul μ ρ hρc (hψ x) v
  let L : W →ₗ[ℂ] V :=
    { toFun := fun x => ∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ
      map_add' := fun x y => by
        simp only [map_add, add_smul]
        exact integral_add (hint x) (hint y)
      map_smul' := fun c x => by
        simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  refine ⟨L.intertwiningMap_of_isIntertwiningMap σ ρ fun h x => ?_, fun x => rfl⟩
  show ∫ g, ψ (σ g⁻¹ (σ h x)) • ρ g v ∂μ = ρ h (∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ)
  calc ∫ g, ψ (σ g⁻¹ (σ h x)) • ρ g v ∂μ
      = ∫ g, ψ (σ (h * g)⁻¹ (σ h x)) • ρ (h * g) v ∂μ :=
        (integral_mul_left_eq_self (fun g => ψ (σ g⁻¹ (σ h x)) • ρ g v) h).symm
    _ = ∫ g, LinearMap.toContinuousLinearMap (ρ h) (ψ (σ g⁻¹ x) • ρ g v) ∂μ := by
        congr 1
        funext g
        rw [LinearMap.coe_toContinuousLinearMap', map_smul, mul_inv_rev, map_mul, map_mul,
          Module.End.mul_apply, Module.End.mul_apply, Representation.inv_self_apply]
    _ = ρ h (∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ) :=
        ContinuousLinearMap.integral_comp_comm _ (hint x)

omit [IsTopologicalGroup G] [μ.IsMulLeftInvariant] in
/-- Applying a linear functional `φ` to `∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ` gives the integral of the
product of coefficients. -/
private lemma integral_mul_eq_apply (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρc : ∀ v, Continuous fun g => ρ g v) (ψ : W →ₗ[ℂ] ℂ)
    (hψ : ∀ x, Continuous fun g => ψ (σ g⁻¹ x)) (φ : Module.Dual ℂ V) (v : V) (x : W) :
    ∫ g, φ (ρ g v) * ψ (σ g⁻¹ x) ∂μ = φ (∫ g, ψ (σ g⁻¹ x) • ρ g v ∂μ) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  rw [← LinearMap.coe_toContinuousLinearMap' φ, ← ContinuousLinearMap.integral_comp_comm _
    (integrable_smul μ ρ hρc (hψ x) v)]
  congr 1
  funext g
  rw [LinearMap.coe_toContinuousLinearMap', map_smul, smul_eq_mul, mul_comm]

/-- Schur orthogonality for inequivalent representations: for linear functionals `φ` on `V` and
`ψ` on `W` with continuous coefficients `g ↦ ψ (σ g w)`, the product of coefficients integrates to
zero. -/
theorem integral_dual_mul_dual_inv_eq_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (hne : IsEmpty (ρ.Equiv σ))
    (hρc : ∀ v, Continuous fun g => ρ g v)
    (φ : Module.Dual ℂ V) (ψ : Module.Dual ℂ W) (hψc : ∀ w, Continuous fun g => ψ (σ g w))
    (v : V) (w : W) :
    ∫ g, φ (ρ g v) * ψ (σ g⁻¹ w) ∂μ = 0 := by
  have : IsEmpty (σ.Equiv ρ) := ⟨fun e => hne.false e.symm⟩
  have hψ : ∀ x, Continuous fun g => ψ (σ g⁻¹ x) := fun x => (hψc x).comp continuous_inv
  obtain ⟨T, hT⟩ := exists_intertwiningMap μ ρ σ hρc ψ hψ v
  have hT0 : T = 0 := Subsingleton.elim _ _
  rw [integral_mul_eq_apply μ ρ σ hρc ψ hψ φ v w, ← hT, hT0,
    Representation.IntertwiningMap.coe_zero, Pi.zero_apply, map_zero]

/-- Schur orthogonality for one representation: for a finite left-invariant measure `μ`,
`∫ g, φ (ρ g v) * ψ (ρ g⁻¹ w) ∂μ = μ(G) * (φ w * ψ v) / dim V`. -/
theorem integral_dual_mul_dual_inv_self (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun g => ρ g v)
    (φ ψ : Module.Dual ℂ V) (v w : V) :
    ∫ g, φ (ρ g v) * ψ (ρ g⁻¹ w) ∂μ =
      (μ.real Set.univ : ℂ) * (φ w * ψ v) / Module.finrank ℂ V := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hψ : ∀ x, Continuous fun g => ψ (ρ g⁻¹ x) := fun x =>
    (LinearMap.continuous_of_finiteDimensional ψ).comp ((hρc x).comp continuous_inv)
  obtain ⟨T, hT⟩ := exists_intertwiningMap μ ρ ρ hρc ψ hψ v
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 T
  have hTc : ∀ x, T x = c • x := fun x => by
    rw [← hc, Representation.IntertwiningMap.algebraMap_apply]
    rfl
  have hlin : T.toLinearMap = c • LinearMap.id := LinearMap.ext fun x => hTc x
  let b := Module.finBasis ℂ V
  have htr : (Module.finrank ℂ V : ℂ) * c = (μ.real Set.univ : ℂ) * ψ v := by
    calc (Module.finrank ℂ V : ℂ) * c = LinearMap.trace ℂ V T.toLinearMap := by
          rw [hlin, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
      _ = ∑ i, b.coord i (T (b i)) := by
          rw [LinearMap.trace_eq_matrix_trace ℂ b]
          refine Fintype.sum_congr _ _ fun i => ?_
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
          rfl
      _ = ∑ i, ∫ g, b.coord i (ψ (ρ g⁻¹ (b i)) • ρ g v) ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hT, ← LinearMap.coe_toContinuousLinearMap' (b.coord i),
            ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul μ ρ hρc (hψ (b i)) v)]
      _ = ∫ g, ∑ i, b.coord i (ψ (ρ g⁻¹ (b i)) • ρ g v) ∂μ := by
          refine (integral_finsetSum _ fun i _ => ?_).symm
          rw [← LinearMap.coe_toContinuousLinearMap' (b.coord i)]
          exact ContinuousLinearMap.integrable_comp _ (integrable_smul μ ρ hρc (hψ (b i)) v)
      _ = ∫ _g, ψ v ∂μ := by
          congr 1
          funext g
          calc ∑ i, b.coord i (ψ (ρ g⁻¹ (b i)) • ρ g v)
              = ψ (ρ g⁻¹ (∑ i, b.repr (ρ g v) i • b i)) := by
                rw [map_sum, map_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [map_smul, map_smul, map_smul, Module.Basis.coord_apply, smul_eq_mul,
                  smul_eq_mul, mul_comm]
            _ = ψ v := by rw [b.sum_repr, Representation.inv_self_apply]
      _ = (μ.real Set.univ : ℂ) * ψ v := by rw [integral_const, Complex.real_smul]
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [integral_mul_eq_apply μ ρ ρ hρc ψ hψ φ v w, ← hT, hTc, map_smul, smul_eq_mul,
    eq_div_iff hd]
  linear_combination φ w * htr

end D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
