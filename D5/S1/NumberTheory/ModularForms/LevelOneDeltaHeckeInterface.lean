/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The level-one discriminant and a prime Hecke coefficient interface

The weight-12 level-one cusp space is one-dimensional, and the modular
discriminant has first q-expansion coefficient `1`.  This file packages the
formal consequence that any *actual* prime Hecke operator satisfying the
standard coefficient law acts on `Δ` by a scalar and therefore yields the
Ramanujan recurrence.

The operator itself is intentionally an input.  Mathlib currently supplies the
level-one q-expansion and rank-one APIs used here, but does not expose the
analytic Hecke action needed to instantiate this interface.  Thus the theorem
marks the exact missing bridge without treating the Lehmer conjecture as proved.
-/

open UpperHalfPlane ModularForm ModularFormClass CuspFormClass MatrixGroups
open scoped BigOperators

namespace D5.S1.NumberTheory.ModularForms

noncomputable section

local notation "Δ" => CuspForm.discriminant

abbrev DeltaCuspForm := CuspForm 𝒮ℒ 12

theorem levelOne_cuspForm_eq_smul_delta (f : DeltaCuspForm) :
    ∃ c : ℂ, c • Δ = f :=
  CuspForm.exists_smul_discriminant_of_weight_eq_twelve f

theorem levelOne_delta_prime_hecke_qExpansion_recurrence
    {p : ℕ} (hp : p.Prime)
    (H : DeltaCuspForm →ₗ[ℂ] DeltaCuspForm)
    (hCoeff : ∀ (f : DeltaCuspForm) (n : ℕ),
      (qExpansion 1 (H f)).coeff n =
        (qExpansion 1 f).coeff (p * n) +
          (p : ℂ) ^ 11 *
            if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) :
    ∃ c : ℂ,
      c = (qExpansion 1 (H Δ)).coeff 1 ∧
      ∀ n : ℕ,
        c * (qExpansion 1 Δ).coeff n =
          (qExpansion 1 Δ).coeff (p * n) +
            (p : ℂ) ^ 11 *
              if p ∣ n then (qExpansion 1 Δ).coeff (n / p) else 0 := by
  have _hp : p.Prime := hp
  obtain ⟨c, hc⟩ := levelOne_cuspForm_eq_smul_delta (H Δ)
  have hc_one : c = (qExpansion 1 (H Δ)).coeff 1 := by
    have h := congrArg (fun f : DeltaCuspForm => (qExpansion 1 f).coeff 1) hc
    change (qExpansion 1 (c • (Δ : ℍ → ℂ))).coeff 1 =
      (qExpansion 1 (H Δ)).coeff 1 at h
    rw [qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero Δ one_pos
        one_mem_strictPeriods_SL) c,
      PowerSeries.coeff_smul] at h
    change c • (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 1 =
      (qExpansion 1 (H Δ)).coeff 1 at h
    rw [discriminant_qExpansion_coeff_one, smul_eq_mul] at h
    simpa using h
  refine ⟨c, hc_one, ?_⟩
  intro n
  have hc_n : c * (qExpansion 1 Δ).coeff n =
      (qExpansion 1 (H Δ)).coeff n := by
    have h := congrArg (fun f : DeltaCuspForm => (qExpansion 1 f).coeff n) hc
    change (qExpansion 1 (c • (Δ : ℍ → ℂ))).coeff n =
      (qExpansion 1 (H Δ)).coeff n at h
    rw [qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero Δ one_pos
        one_mem_strictPeriods_SL) c,
      PowerSeries.coeff_smul, smul_eq_mul] at h
    simpa using h
  rw [hc_n, hCoeff]

end

end D5.S1.NumberTheory.ModularForms

#print axioms D5.S1.NumberTheory.ModularForms.levelOne_cuspForm_eq_smul_delta
#print axioms D5.S1.NumberTheory.ModularForms.levelOne_delta_prime_hecke_qExpansion_recurrence
