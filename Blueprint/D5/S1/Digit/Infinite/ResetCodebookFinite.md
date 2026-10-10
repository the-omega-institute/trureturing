# Reset codebook: Finite

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Theorem 1.1 (common memory cutoff).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.common_memory_cutoff`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.common_memory_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (height eps : ℝ) (hh : 0 < height) (heps : 0 < eps) : ∃ n : ℕ, K ≤ n ∧ height*rho^n < eps

**Definition 1.2 (step).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.step`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by step(low : Bool) (D : ℝ) := A low+rho*D.

**Definition 1.3 (run).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.run`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by run(low : Bool) (a : Return) (D : ℝ) := (step low)^[a.val.1] (chi^a.val.2*D).

**Theorem 1.4 (parameters).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.parameters`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) : 0 < rho ∧ rho < 1 ∧ 0 < chi ∧ chi < 1 ∧ 0 < h low ∧ h low < E low ∧ E low ≤ 1/4

**Definition 1.5 (execute).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.execute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by execute(low : Bool) (as : List Return) (D : ℝ) := as.foldl (fun x a => run low a x) D.

**Theorem 1.6 (run bounds).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.run_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (a : Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) : 0 ≤ run low a D ∧ run low a D ≤ h low

**Theorem 1.7 (execute bounds).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (as : List Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) : 0 ≤ execute low as D ∧ execute low as D ≤ h low

**Definition 1.8 (initial).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.initial`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by initial(low anchor : Bool) := if anchor then Y low else X low.

**Definition 1.9 (closedRun).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.closedRun`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.closedRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by closedRun(low : Bool) (m r : ℕ) (D : ℝ) := h low-rho^m*(h low-chi^r*D).

**Theorem 1.10 (run closed).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_closed`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.run_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (a : Return) (D : ℝ) : run low a D=closedRun low a.val.1 a.val.2 D

**Theorem 1.11 (reset lifts).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_lifts`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (M : ℕ) (z : ℝ) (hz : A false ≤ z) : resetFloor M ≤ closedRun false M 1 z

**Theorem 1.12 (execute floor).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_floor`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (as : List Return) (D : ℝ) (hD : A low ≤ D) (hh : D ≤ h low) : A low ≤ execute low as D

**Theorem 1.13 (weak run).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_run`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (d : ℝ) (a : Return) (as : List Return) (D : ℝ) : Statement.weak K d (a::as) D ↔ a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ Statement.weak K d as (run false a D)

**Theorem 1.14 (weak gain).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_gain`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (d delta x y : ℝ) (as : List Return) (hd : 0 < delta) (hxy : x+delta ≤ y) (hw : Statement.weak K d as x) : Statement.weak K (d+delta*g^(totalWeight as)) as y

**Theorem 1.15 (A nonneg).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.A_nonneg`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.A_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: 0 ≤ A false

**Theorem 1.16 (weak append).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_append`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two weak runs meet at the state produced by executing the first list, their concatenation is weak from the initial state.

**Theorem 1.17 (finite reset weak state).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.finite_reset_weak_state`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.finite_reset_weak_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite list of codeword lists, the reset-prefixed concatenation satisfies the strengthened weak guard at every state between A false and h false, provided each codeword has weight N and satisfies the original weak guard.

**Theorem 1.18 (reset actual family).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_actual_family`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_actual_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hb : lambda-g^2*chi^K*h false < b) (hd : d=(lambda-b)/(g^2*chi^K)) (hreset : max (X false) (Y false) < Statement.B M) : 0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.A_nonneg`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.closedRun`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.common_memory_cutoff`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_bounds`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_floor`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.finite_reset_weak_state`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.initial`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.parameters`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_actual_family`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_lifts`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.run`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_bounds`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_closed`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.step`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_append`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_gain`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_run`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookGrowth](ResetCodebookGrowth.md)
