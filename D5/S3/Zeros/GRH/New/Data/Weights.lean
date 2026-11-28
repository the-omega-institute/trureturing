/- GID: D5/S3/Zeros/GRH/New/Data/Weights
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/Weights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.Weights. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/Weights.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Data.Magnitudes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Size comparisons among nominal weights and weights of the lifts. -/

open Real Set

namespace Data

variable {P} (D : Data P) {j : ℕ} (hj : j ≤ 2 * D.m) (σ : D.Φ)
attribute [local simp] w nominalWeight b₁ b₂

lemma nominalWeight_mem_Icc :
  D.nominalWeight σ ∈ Icc (D.a / D.x₁) (D.a / D.x) := by
  simp [mem_Icc]; split <;> simp_all <;> use D.le_of_hasLogBound

instance {u} : D.HasLogBound u (D.nominalWeight σ) (D.logB + ite u 1 (-D.logX₁)) :=
  .of_mem_Icc _ _ (nominalWeight_mem_Icc ..)

@[simp, bound] lemma nominalWeight_nonneg : 0 ≤ D.nominalWeight σ := (HasLogBound.pos D).le

/-- At every infinite place σ of E, the nominal weight w(σ) = `Data.nominalWeight` σ satisfies w(σ)
+ x⁴² ≤ 2b. -/
lemma nominalWeight_add_le : D.nominalWeight σ + D.x ^ 42 ≤ 2 * D.b := by
  grw [(nominalWeight_mem_Icc ..).2, a, D.roundUp_mem_Icc.2, two_mul, add_div,
    add_assoc]; simpa using D.le_of_hasLogBound

lemma nominalWeight_le_w_sub j σ : D.nominalWeight σ ≤
  D.w j σ - D.h₂ := by simp; split <;> grw [← D.roundUp_mem_Icc.1] <;> bound

include hj

/-- For j ≤ 2m and every infinite place σ of E, the weight w_j(σ) exceeds the nominal weight
w(σ) by at most x^42. -/
lemma w_le_nominalWeight_add : D.w j σ ≤ D.nominalWeight σ + D.x ^ 42 := by
  simp; split <;> grw [hj, D.roundUp_mem_Icc.2] <;> simpa [add_assoc] using D.le_of_hasLogBound

/-- For j ≤ 2m and every infinite place σ of E, the weight w_j(σ) is at most 2b. -/
lemma w_le_two_mul_b :
  D.w j σ ≤ 2 * D.b := by grw [w_le_nominalWeight_add _ hj, nominalWeight_add_le]

instance : D.HasLogUpper (D.w 0 σ) (2 + D.logB) :=
  hasLogUpper_of_le_of_nonneg (D.w_le_two_mul_b bot_le _)

instance {l} [D.HasLogLower (D.nominalWeight σ) l] :
  D.HasLogLower (D.w j σ) l := by grind [HasLogBound, D.nominalWeight_le_w_sub j σ]

/-- For j ≤ 2m and every infinite place σ of E, log w_j(σ) ≤ log w(σ) + 1/x, where w_j is the j-th
weight and w = `Data.nominalWeight` is the nominal weight. -/
lemma log_w_le : log (D.w j σ) ≤ log (D.nominalWeight σ) + D.x⁻¹ := by
  grw [log_le_iff_le_exp, w_le_nominalWeight_add _ hj, exp_add, exp_log, ← add_one_le_exp, mul_add,
    add_comm] <;> simp [HasLogBound.pos D, -nominalWeight, -w]
  exact D.le_of_hasLogBound
