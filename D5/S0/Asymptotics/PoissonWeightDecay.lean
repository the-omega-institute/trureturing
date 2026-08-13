/- GID: D5/S0/Asymptotics/PoissonWeightDecay
   generality: G
   mirror-B: D5/B/S0/Asymptotics/PoissonWeightDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Geometric listing weights tend to zero, excluding positive limits. -/

import Mathlib.Analysis.SpecificLimits.Normed

namespace D5.S0.Asymptotics.PoissonWeightDecay

open Filter

/-- For fixed `n >= 2` and `k <= n`, the weight `k * A * n^(-A)` obeys the
source's geometric envelope, tends to zero, and therefore cannot tend to a
positive real value. This is clause (iv) of the source corollary; its other
asymptotic and finite clauses remain outside this partial closure. -/
theorem poisson_weight_tendsto_zero (n k : Nat) (hn : 2 <= n) (hk : k <= n) :
    (forall A : Nat,
      0 <= (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) /\
      (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) <=
        (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) /\
      (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) <=
        (A : Real) * 2 * ((2 : Real)⁻¹ ^ A)) /\
    Tendsto (fun A : Nat => (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A))
        atTop (nhds 0) /\
      forall lambda : Real, 0 < lambda ->
        Not (Tendsto (fun A : Nat => (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A))
          atTop (nhds lambda)) := by
  have hn_real : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hn_pos : (0 : Real) < n := by linarith
  have hn_one : (1 : Real) < n := by linarith
  have h_inv_nonneg : (0 : Real) <= (n : Real)⁻¹ := inv_nonneg.mpr hn_pos.le
  have h_inv_lt_one : (n : Real)⁻¹ < 1 := (inv_lt_one₀ hn_pos).mpr hn_one
  have h_inv_le_half : (n : Real)⁻¹ <= (2 : Real)⁻¹ :=
    (inv_le_inv₀ hn_pos (by norm_num)).mpr hn_real
  have hk_real : (k : Real) <= (n : Real) := by exact_mod_cast hk
  have hbounds : forall A : Nat,
      0 <= (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) /\
      (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) <=
        (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) /\
      (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) <=
        (A : Real) * 2 * ((2 : Real)⁻¹ ^ A) := by
    intro A
    constructor
    · positivity
    constructor
    · have hA : (0 : Real) <= A := by positivity
      have hpow : (0 : Real) <= (n : Real)⁻¹ ^ A := pow_nonneg h_inv_nonneg A
      calc
        (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) =
            (A : Real) * (k : Real) * ((n : Real)⁻¹ ^ A) := by ring
        _ <= (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk_real hA) hpow
    · cases A with
      | zero => norm_num
      | succ A =>
          have hpow : (n : Real)⁻¹ ^ A <= (2 : Real)⁻¹ ^ A :=
            pow_le_pow_left₀ h_inv_nonneg h_inv_le_half A
          calc
            ((A + 1 : Nat) : Real) * (n : Real) * ((n : Real)⁻¹ ^ (A + 1)) =
                ((A + 1 : Nat) : Real) * ((n : Real)⁻¹ ^ A) := by
                  rw [pow_succ]
                  field_simp
            _ <= ((A + 1 : Nat) : Real) * ((2 : Real)⁻¹ ^ A) := by
                  exact mul_le_mul_of_nonneg_left hpow (by positivity)
            _ = ((A + 1 : Nat) : Real) * 2 * ((2 : Real)⁻¹ ^ (A + 1)) := by
                  rw [pow_succ]
                  ring
  have hdecay :
      Tendsto (fun A : Nat => (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A))
        atTop (nhds 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_self_mul_const_pow_of_lt_one h_inv_nonneg h_inv_lt_one).const_mul (k : Real)
  refine ⟨hbounds, hdecay, fun lambda hlambda hlambda_limit => ?_⟩
  have : lambda = 0 := tendsto_nhds_unique hlambda_limit hdecay
  linarith

/-- The natural-number domain and the source conditions are simultaneously inhabited. -/
example : exists n k : Nat, 2 <= n /\ k <= n := ⟨2, 1, by decide, by decide⟩

end D5.S0.Asymptotics.PoissonWeightDecay
