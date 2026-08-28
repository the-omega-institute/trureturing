/- GID: D5/S3/Quantum/Decoherence/RecordActionCoherenceSurvival
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/RecordActionCoherenceSurvival
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized record overlaps control coherence survival and its logarithmic rate. -/

import D5.S3.Quantum.PureState.RecordCoherenceComplementarity
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.ENNReal.Inv

/- Library-search audit trail (2026-08-28):
   * Repository searches found the canonical finite `recordGram`, homogeneous repeated-record
     channel laws, and the Hilbert-space overlap bound in `RecordCoherenceComplementarity`, but
     no cumulative record action or logarithmic erasure-rate theorem.
   * Body-shape searches for a product over `Finset.range`, its negative extended logarithm, and
     a record-action definition were misses, so the source objects are constructed as public
     `let` bindings directly from record-vector inner products.
   * Pinned Mathlib supplies `norm_inner_le_norm`, `norm_prod`, `ENNReal.exp_log`,
     `EReal.coe_toENNReal`, and `ENNReal.mul_div_cancel_right`; no exact theorem assembles the
     survival identity, action monotonicity, and asymptotic rate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ENNReal InnerProductSpace
open Filter

namespace D5.S3.Quantum.Decoherence.RecordActionCoherenceSurvival

/-- Finite normalized environment records multiply a selected coherence coordinate by their
cumulative Gram overlap. The nonnegative extended negative logarithm of that overlap gives the
exact exponential survival factor, increases with the record count, and has the same asymptotic
rate as the logarithmic relative coherence. -/
theorem record_action_controls_coherence_survival
    {Address Environment : Type*}
    [NormedAddCommGroup Environment] [InnerProductSpace Complex Environment]
    (record : Nat -> Address -> Environment)
    (recordNormalized : forall (r : Nat) (i : Address), ‖record r i‖ = 1)
    (i j : Address) (rhoInitial : Complex) (rhoInitialNonzero : rhoInitial ≠ 0) :
    let overlap : Nat -> Complex := fun r => ⟪record r j, record r i⟫_Complex
    let cumulativeOverlap : Nat -> Complex := fun N =>
      ∏ r ∈ Finset.range N, overlap r
    let recordAction : Nat -> ENNReal := fun N =>
      (-ENNReal.log (ENNReal.ofReal ‖cumulativeOverlap N‖)).toENNReal
    let rho : Nat -> Complex := fun N => cumulativeOverlap N * rhoInitial
    (forall N,
        ENNReal.ofReal ‖rho N‖ =
          EReal.exp (-(recordAction N : EReal)) * ENNReal.ofReal ‖rhoInitial‖) /\
      Monotone recordAction /\
      forall lambda : EReal,
        Tendsto (fun N => (recordAction N : EReal) / (N : EReal)) atTop (nhds lambda) ->
          Tendsto (fun N =>
            -ENNReal.log
                (ENNReal.ofReal ‖rho N‖ / ENNReal.ofReal ‖rhoInitial‖) /
              (N : EReal)) atTop (nhds lambda) := by
  dsimp only
  let overlap : Nat -> Complex := fun r => ⟪record r j, record r i⟫_Complex
  let cumulativeOverlap : Nat -> Complex := fun N =>
    ∏ r ∈ Finset.range N, overlap r
  let survival : Nat -> ENNReal := fun N => ENNReal.ofReal ‖cumulativeOverlap N‖
  let recordAction : Nat -> ENNReal := fun N =>
    (-ENNReal.log (survival N)).toENNReal
  let rho : Nat -> Complex := fun N => cumulativeOverlap N * rhoInitial
  have overlapBound (r : Nat) : ‖overlap r‖ <= 1 := by
    calc
      ‖overlap r‖ <= ‖record r j‖ * ‖record r i‖ := by
        exact norm_inner_le_norm (record r j) (record r i)
      _ = 1 := by rw [recordNormalized r j, recordNormalized r i, one_mul]
  have survivalLeOne (N : Nat) : survival N <= 1 := by
    change ENNReal.ofReal ‖∏ r ∈ Finset.range N, overlap r‖ <= 1
    rw [norm_prod]
    have productBound : (∏ r ∈ Finset.range N, ‖overlap r‖) <= 1 := by
      calc
        (∏ r ∈ Finset.range N, ‖overlap r‖) <=
            ∏ _r ∈ Finset.range N, (1 : Real) := by
          exact Finset.prod_le_prod
            (fun _ _ => norm_nonneg _)
            (fun r _ => overlapBound r)
        _ = 1 := by simp
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal productBound
  have actionCoe (N : Nat) :
      (recordAction N : EReal) = -ENNReal.log (survival N) := by
    apply EReal.coe_toENNReal
    exact EReal.neg_nonneg.mpr (ENNReal.log_le_zero_iff.mpr (survivalLeOne N))
  have exponentialAction (N : Nat) :
      EReal.exp (-(recordAction N : EReal)) = survival N := by
    rw [actionCoe]
    simp
  have survivalStep (N : Nat) : survival (N + 1) <= survival N := by
    change ENNReal.ofReal ‖∏ r ∈ Finset.range (N + 1), overlap r‖ <=
      ENNReal.ofReal ‖∏ r ∈ Finset.range N, overlap r‖
    rw [Finset.prod_range_succ, norm_mul,
      ENNReal.ofReal_mul (norm_nonneg (∏ r ∈ Finset.range N, overlap r))]
    simpa using mul_le_mul_right
      (show ENNReal.ofReal ‖overlap N‖ <= 1 by
        simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (overlapBound N))
      (ENNReal.ofReal ‖∏ r ∈ Finset.range N, overlap r‖)
  have actionMonotone : Monotone recordAction := by
    exact monotone_nat_of_le_succ fun N =>
      EReal.toENNReal_le_toENNReal
        (EReal.neg_le_neg_iff.mpr (ENNReal.log_le_log (survivalStep N)))
  have survivalIdentity (N : Nat) :
      ENNReal.ofReal ‖rho N‖ =
        EReal.exp (-(recordAction N : EReal)) * ENNReal.ofReal ‖rhoInitial‖ := by
    change ENNReal.ofReal ‖cumulativeOverlap N * rhoInitial‖ = _
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg (cumulativeOverlap N)),
      exponentialAction]
  have initialMagnitudeNonzero : ENNReal.ofReal ‖rhoInitial‖ ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr rhoInitialNonzero)
  have relativeCoherence (N : Nat) :
      ENNReal.ofReal ‖rho N‖ / ENNReal.ofReal ‖rhoInitial‖ = survival N := by
    rw [survivalIdentity, exponentialAction]
    exact ENNReal.mul_div_cancel_right initialMagnitudeNonzero ENNReal.ofReal_ne_top
  refine ⟨survivalIdentity, actionMonotone, ?_⟩
  intro lambda actionRate
  apply actionRate.congr'
  filter_upwards [] with N
  rw [relativeCoherence, actionCoe]

example :
    Exists fun record : Nat -> Unit -> Complex =>
      (forall (r : Nat) (i : Unit), ‖record r i‖ = 1) /\
        (1 : Complex) ≠ 0 := by
  exact ⟨fun _ _ => 1, by simp, one_ne_zero⟩

#print axioms record_action_controls_coherence_survival

end D5.S3.Quantum.Decoherence.RecordActionCoherenceSurvival
