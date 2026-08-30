/- GID: D5/S3/Observer/Linear/FiniteObservabilityEnergyBalance
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/FiniteObservabilityEnergyBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observability identity, Gramian positivity, and state energy balance. -/

import Mathlib.Analysis.InnerProductSpace.Positive

/- Library-search audit trail (2026-08-31):
   * D5 searches found finite observability rank and discounted Gramian results,
     but no theorem combining this finite telescoping identity, positivity, and
     the state norm balance under the conservation law.
   * Body-shape searches found no canonical finite Gramian construction in the
     Observer/Linear family; the finite sum below is therefore constructed
     directly from the source maps A and C.
   * Pinned Mathlib hits `star_pow`, `Finset.sum_range_sub'`,
     `ContinuousLinearMap.isPositive_adjoint_comp_self`, and
     `ContinuousLinearMap.adjoint_inner_right` provide the adjoint-power,
     telescoping, operator-positivity, and energy steps.
   * Pinned Mathlib search found no packaged finite observability identity.
 -/

open scoped InnerProduct InnerProductSpace BigOperators
open InnerProductSpace RCLike
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.FiniteObservabilityEnergyBalance

variable {𝕜 V Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

/-- The finite observability Gramian telescopes under a conservative update/readout
system, is positive semidefinite, and measures the corresponding state energy loss. -/
theorem finite_observability_energy_balance
    (A : V →L[𝕜] V) (C : V →L[𝕜] Y) (N : ℕ)
    (hconserve : A† ∘L A + C† ∘L C = ContinuousLinearMap.id 𝕜 V) :
    ContinuousLinearMap.id 𝕜 V - (A ^ N)† ∘L (A ^ N) =
      (∑ k ∈ Finset.range N,
        (((A ^ k)† ∘L (C† ∘L C)) ∘L (A ^ k))) ∧
    (∑ k ∈ Finset.range N,
      (((A ^ k)† ∘L (C† ∘L C)) ∘L (A ^ k))).IsPositive ∧
    ∀ x : V, ‖x‖ ^ 2 - ‖(A ^ N) x‖ ^ 2 =
      ∑ k ∈ Finset.range N, ‖C ((A ^ k) x)‖ ^ 2 := by
  have hcc : C† ∘L C = ContinuousLinearMap.id 𝕜 V - A† ∘L A := by
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hconserve)
  have hadjpow : ∀ k : ℕ,
      (A ^ k)† = (A†) ^ k := by
    intro k
    change star (A ^ k) = star A ^ k
    exact star_pow A k
  have hterm : ∀ k : ℕ,
      (((A ^ k)† ∘L (C† ∘L C)) ∘L (A ^ k)) =
        (A ^ k)† ∘L (A ^ k) - (A ^ (k + 1))† ∘L (A ^ (k + 1)) := by
    intro k
    rw [hcc, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_assoc, hadjpow k]
    have hnext : (A ^ (k + 1))† = ((A†) ^ k) ∘L A† := by
      rw [hadjpow (k + 1), pow_succ]
      ext x
      rfl
    rw [hnext, pow_succ']
    ext x
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      mul_apply_eq_comp]
  constructor
  · rw [Finset.sum_congr rfl (fun k hk => hterm k)]
    have htel := Finset.sum_range_sub'
      (fun k : ℕ => (A ^ k)† ∘L (A ^ k)) N
    rw [htel]
    ext x
    simp
  constructor
  · apply ContinuousLinearMap.isPositive_sum
    intro k hk
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] using
      (ContinuousLinearMap.isPositive_adjoint_comp_self (C ∘L (A ^ k)))
  · intro x
    have henergy : ∀ y : V, ‖y‖ ^ 2 = ‖A y‖ ^ 2 + ‖C y‖ ^ 2 := by
      intro y
      have hA := ContinuousLinearMap.adjoint_inner_right A y (A y)
      have hC := ContinuousLinearMap.adjoint_inner_right C y (C y)
      calc
        ‖y‖ ^ 2 = RCLike.re (inner 𝕜 y y) :=
          (inner_self_eq_norm_sq y).symm
        _ = RCLike.re (inner 𝕜 y ((ContinuousLinearMap.id 𝕜 V) y)) := by
          rfl
        _ = RCLike.re (inner 𝕜 y
            ((A† ∘L A + C† ∘L C) y)) := by
          rw [hconserve]
        _ = RCLike.re (inner 𝕜 y ((A† ∘L A) y)) +
            RCLike.re (inner 𝕜 y ((C† ∘L C) y)) := by
          change RCLike.reCLM
              (inner 𝕜 y
                ((A† ∘L A) y + (C† ∘L C) y)) = _
          rw [inner_add_right, map_add]
          rfl
        _ = ‖A y‖ ^ 2 + ‖C y‖ ^ 2 := by
          rw [ContinuousLinearMap.comp_apply, hA, ContinuousLinearMap.comp_apply, hC,
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

-- Each public clause remains independently usable; positivity needs no conservation premise.
example (A : V →L[𝕜] V) (C : V →L[𝕜] Y) (N : ℕ)
    (hconserve : A† ∘L A + C† ∘L C = ContinuousLinearMap.id 𝕜 V) :
    ContinuousLinearMap.id 𝕜 V - (A ^ N)† ∘L (A ^ N) =
      ∑ k ∈ Finset.range N,
        (((A ^ k)† ∘L (C† ∘L C)) ∘L (A ^ k)) :=
  (finite_observability_energy_balance A C N hconserve).1

example (A : V →L[𝕜] V) (C : V →L[𝕜] Y) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (((A ^ k)† ∘L (C† ∘L C)) ∘L (A ^ k))).IsPositive := by
  apply ContinuousLinearMap.isPositive_sum
  intro k hk
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.isPositive_adjoint_comp_self (C ∘L (A ^ k)))

example (A : V →L[𝕜] V) (C : V →L[𝕜] Y) (N : ℕ)
    (hconserve : A† ∘L A + C† ∘L C = ContinuousLinearMap.id 𝕜 V) (x : V) :
    ‖x‖ ^ 2 - ‖(A ^ N) x‖ ^ 2 =
      ∑ k ∈ Finset.range N, ‖C ((A ^ k) x)‖ ^ 2 :=
  (finite_observability_energy_balance A C N hconserve).2.2 x

#print axioms finite_observability_energy_balance

end D5.S3.Observer.Linear.FiniteObservabilityEnergyBalance
