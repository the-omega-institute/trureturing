/- GID: D5/S3/Observer/Linear/FiniteObservabilityEnergyBalance
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/FiniteObservabilityEnergyBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observability identity, Gramian positivity, and state energy balance. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/- Library-search audit trail (2026-08-31):
   * D5 searches found finite observability rank and discounted Gramian results,
     but no theorem combining this finite telescoping identity, positivity, and
     the state norm balance under the conservation law.
   * Body-shape searches found no canonical finite Gramian construction in the
     Observer/Linear family; the finite sum below is therefore constructed
     directly from the source maps A and C.
   * Pinned Mathlib hits `star_pow`, `Finset.sum_range_sub'`,
     `LinearMap.adjoint_inner_right`, and `inner_self_eq_norm_sq` provide the
     adjoint-power, telescoping, and quadratic-form steps.
   * Pinned Mathlib search found no packaged finite observability identity.
 -/

open scoped InnerProductSpace BigOperators
open InnerProductSpace RCLike
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.FiniteObservabilityEnergyBalance

variable {𝕜 V Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]

/-- The finite observability Gramian telescopes under a conservative update/readout
system, is positive semidefinite, and measures the corresponding state energy loss. -/
theorem finite_observability_energy_balance
    (A : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (N : ℕ)
    (hconserve : (LinearMap.adjoint A).comp A + (LinearMap.adjoint C).comp C =
      LinearMap.id) :
    LinearMap.id - (LinearMap.adjoint (A ^ N)).comp (A ^ N) =
      (∑ k ∈ Finset.range N,
        ((LinearMap.adjoint (A ^ k)).comp ((LinearMap.adjoint C).comp C)).comp (A ^ k)) ∧
    (∀ x : V, 0 ≤ RCLike.re (inner 𝕜 x
      ((∑ k ∈ Finset.range N,
        ((LinearMap.adjoint (A ^ k)).comp ((LinearMap.adjoint C).comp C)).comp (A ^ k)) x))) ∧
    ∀ x : V, ‖x‖ ^ 2 - ‖(A ^ N) x‖ ^ 2 =
      ∑ k ∈ Finset.range N, ‖C ((A ^ k) x)‖ ^ 2 := by
  have hcc : (LinearMap.adjoint C).comp C =
      LinearMap.id - (LinearMap.adjoint A).comp A := by
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hconserve)
  have hadjpow : ∀ k : ℕ,
      LinearMap.adjoint (A ^ k) = (LinearMap.adjoint A) ^ k := by
    intro k
    change star (A ^ k) = star A ^ k
    exact star_pow A k
  have hterm : ∀ k : ℕ,
      ((LinearMap.adjoint (A ^ k)).comp ((LinearMap.adjoint C).comp C)).comp (A ^ k) =
        (LinearMap.adjoint (A ^ k)).comp (A ^ k) -
          (LinearMap.adjoint (A ^ (k + 1))).comp (A ^ (k + 1)) := by
    intro k
    rw [hcc, LinearMap.comp_sub, LinearMap.sub_comp,
      LinearMap.comp_id, LinearMap.comp_assoc, hadjpow k]
    have hnext : LinearMap.adjoint (A ^ (k + 1)) =
        ((LinearMap.adjoint A) ^ k).comp (LinearMap.adjoint A) := by
      rw [hadjpow (k + 1), pow_succ]
      ext x
      rfl
    rw [hnext, pow_succ']
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.End.mul_apply]
  constructor
  · rw [Finset.sum_congr rfl (fun k hk => hterm k)]
    have htel := Finset.sum_range_sub'
      (fun k : ℕ => (LinearMap.adjoint (A ^ k)).comp (A ^ k)) N
    rw [htel]
    ext x
    simp
  constructor
  · intro x
    rw [LinearMap.sum_apply]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      change 0 ≤ RCLike.reCLM
        (inner 𝕜 x
          (∑ d ∈ Finset.range N,
              (((LinearMap.adjoint (A ^ d)).comp ((LinearMap.adjoint C).comp C)).comp
                (A ^ d)) x +
            (((LinearMap.adjoint (A ^ N)).comp ((LinearMap.adjoint C).comp C)).comp
              (A ^ N)) x))
      rw [inner_add_right, map_add]
      apply add_nonneg ih
      have hA := LinearMap.adjoint_inner_right (A ^ N) x
        ((LinearMap.adjoint C) (C ((A ^ N) x)))
      have hC := LinearMap.adjoint_inner_right C ((A ^ N) x)
        (C ((A ^ N) x))
      calc
        0 ≤ ‖C ((A ^ N) x)‖ ^ 2 := sq_nonneg _
        _ = RCLike.re (inner 𝕜 (C ((A ^ N) x)) (C ((A ^ N) x))) :=
          (inner_self_eq_norm_sq _).symm
        _ = RCLike.re (inner 𝕜 ((A ^ N) x)
            ((LinearMap.adjoint C) (C ((A ^ N) x)))) := by
          rw [hC]
        _ = RCLike.re (inner 𝕜 x
            ((LinearMap.adjoint (A ^ N))
              ((LinearMap.adjoint C) (C ((A ^ N) x))))) := by
          rw [hA]
        _ = RCLike.re (inner 𝕜 x
            ((((LinearMap.adjoint (A ^ N)).comp ((LinearMap.adjoint C).comp C)).comp
              (A ^ N)) x)) := by
          simp only [LinearMap.comp_apply]
  · intro x
    have henergy : ∀ y : V, ‖y‖ ^ 2 = ‖A y‖ ^ 2 + ‖C y‖ ^ 2 := by
      intro y
      have hA := LinearMap.adjoint_inner_right A y (A y)
      have hC := LinearMap.adjoint_inner_right C y (C y)
      calc
        ‖y‖ ^ 2 = RCLike.re (inner 𝕜 y y) :=
          (inner_self_eq_norm_sq y).symm
        _ = RCLike.re (inner 𝕜 y ((LinearMap.id : V →ₗ[𝕜] V) y)) := by
          rfl
        _ = RCLike.re (inner 𝕜 y
            (((LinearMap.adjoint A).comp A + (LinearMap.adjoint C).comp C) y)) := by
          rw [hconserve]
        _ = RCLike.re (inner 𝕜 y ((LinearMap.adjoint A).comp A y)) +
            RCLike.re (inner 𝕜 y ((LinearMap.adjoint C).comp C y)) := by
          change RCLike.reCLM
              (inner 𝕜 y
                ((LinearMap.adjoint A).comp A y + (LinearMap.adjoint C).comp C y)) = _
          rw [inner_add_right, map_add]
          rfl
        _ = ‖A y‖ ^ 2 + ‖C y‖ ^ 2 := by
          rw [LinearMap.comp_apply, hA, LinearMap.comp_apply, hC,
            inner_self_eq_norm_sq, inner_self_eq_norm_sq]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hpow : A ^ (N + 1) = A * A ^ N := pow_succ' A N
      rw [hpow]
      change ‖x‖ ^ 2 - ‖A ((A ^ N) x)‖ ^ 2 = _
      rw [← ih, henergy ((A ^ N) x)]
      ring

#print axioms finite_observability_energy_balance

end D5.S3.Observer.Linear.FiniteObservabilityEnergyBalance
