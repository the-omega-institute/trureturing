/- GID: D5/S0/Asymptotics/EscapeProbability/EscapeRegimeCorollary
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/EscapeRegimeCorollary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed output systems admit only the full-escape large-address regime. -/

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib has no declaration for escape probability, its fixed-point
     scaling regimes, or the combined corollary below.
   * Loogle queries for `escape probability` and `poisson weight tendsto`
     returned no matching declarations.
   * The proof applies the frozen closed form, monotonicity, strict
     monotonicity, fixed-output limit, geometric decay, and dense-scaling
     exclusion theorems. Mathlib's `Fintype.card_subtype_le` supplies the
     fixed-point count bound.
-/

import D5.S0.Asymptotics.DensePhaseUnrealizable
import D5.S0.Asymptotics.EscapeProbability.FixedOutputLimit
import D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit
import D5.S0.Asymptotics.EscapeProbability.StrictAddressMonotonicity
import D5.S0.Asymptotics.PoissonWeightDecay

namespace D5.S0.Asymptotics.EscapeProbability.EscapeRegimeCorollary

open Filter
open D5.S0.Asymptotics.DensePhaseUnrealizable
open D5.S0.Asymptotics.EscapeProbability.FixedOutputLimit
open D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit
open D5.S0.Asymptotics.EscapeProbability.StrictAddressMonotonicity
open D5.S0.Asymptotics.EscapeProbabilityMonotone
open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Asymptotics.PoissonWeightDecay

/-- For a fixed finite output alphabet, the escape probability is one when
there are no fixed points, is nondecreasing on positive address counts, and has
the stated one-address value. If the alphabet has at least two elements, the
probability is strictly increasing when a fixed point exists and tends to one.
The fixed-point weight then tends to zero and cannot have a positive limit,
while positive-density scaling is eventually impossible. -/
theorem escape_probability_realizable_regimes
    {Y : Type*} [Fintype Y] [Nonempty Y] (f : Y -> Y) :
    let n : Nat := Fintype.card Y
    let k : Nat := Nat.card {y : Y // f y = y}
    (k = 0 -> forall A : Nat,
      escapeProbability (A := Fin A) f = 1) /\
    MonotoneOn (fun A : Nat => escapeProbability (A := Fin A) f)
      (Set.Ici 1) /\
    (2 <= n -> 0 < k -> StrictMonoOn
      (fun A : Nat => escapeProbability (A := Fin A) f) (Set.Ici 1)) /\
    escapeProbability (A := Fin 1) f =
      1 - (k : Real) / (n : Real) /\
    (2 <= n -> Tendsto
      (fun A : Nat => escapeProbability (A := Fin A) f)
      atTop (nhds 1)) /\
    k <= n /\
    (2 <= n ->
      ((forall A : Nat,
        0 <= (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) /\
        (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A) <=
          (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) /\
        (A : Real) * (n : Real) * ((n : Real)⁻¹ ^ A) <=
          (A : Real) * 2 * ((2 : Real)⁻¹ ^ A)) /\
      Tendsto (fun A : Nat =>
        (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A))
        atTop (nhds 0) /\
      forall lambda : Real, 0 < lambda ->
        Not (Tendsto (fun A : Nat =>
          (k : Real) * (A : Real) * ((n : Real)⁻¹ ^ A))
          atTop (nhds lambda)))) /\
    (2 <= n -> forall c : Real, c ∈ Set.Ioo 0 1 ->
      exists A0 : Nat, forall A : Nat, A0 <= A ->
        (k : Real) ≠ c * (n : Real) ^ A) := by
  classical
  dsimp only
  have hk : Nat.card {y : Y // f y = y} <= Fintype.card Y := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  refine ⟨?_, escape_probability_monotone_on_guarded_domain f,
    ?_, escape_probability_one_address f, ?_, hk, ?_, ?_⟩
  · intro hzero A
    rw [escape_probability_closed_form f A, hzero]
    simp
  · intro hn hpositive
    exact escape_probability_strictMonoOn_of_has_fixed_point f hn hpositive
  · intro hn
    exact fixed_output_large_address_escape_probability f hn
  · intro hn
    exact poisson_weight_tendsto_zero (Fintype.card Y)
      (Nat.card {y : Y // f y = y}) hn hk
  · intro hn c hc
    exact (fixed_point_dense_phase_eventually_unrealizable
      f (Fintype.card Y) hn (by rw [Nat.card_eq_fintype_card]) c hc).2

/- A two-element output alphabet with the identity twist witnesses the theorem's
domain and its positive-fixed-point branch. -/
example : exists f : Fin 2 -> Fin 2,
    2 <= Fintype.card (Fin 2) /\
      0 < Nat.card {y : Fin 2 // f y = y} := by
  exact ⟨id, by decide, by simp [Nat.card_eq_fintype_card]⟩

#print axioms escape_probability_realizable_regimes

end D5.S0.Asymptotics.EscapeProbability.EscapeRegimeCorollary
