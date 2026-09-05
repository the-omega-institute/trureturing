/- GID: D5/S1/Recurrence/Witt/GoldenCyclotomicTable
   generality: I
   mirror-B: D5/B/S1/Recurrence/Witt/GoldenCyclotomicTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden word series has the stated signed Witt table through total degree five. -/

import D5.S1.Recurrence.BivariateWordSeries
import Mathlib.Tactic

/- Duplicate-search audit (2026-09-04):
   * Exact and spelling-variant D5 searches covered golden/cyclotomic/Witt
     tables, signed Euler factors, and each of e22, e41, e32, and e23.
   * The digestion and digest indices leave the source atom residual-open;
     the retired formalization-receipt directory is absent and was not used.
   * Generalized searches found the frozen bivariate word-series equation,
     all-order pure and first-row laws, a generic primitive Euler ledger,
     and analytic second-to-fourth ledgers, but no degree-five signed table.
   * The source atom is absent from the in-flight atom index, and no in-flight
     module has the proposed name or an equivalent degree-five table.
   * Pinned Mathlib supplies finite convolution and decision procedures, but
     no theorem for this golden cyclotomic table. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Witt.GoldenCyclotomicTable

open D5.S1.Recurrence.BivariateWordSeries
open Finset
open scoped BigOperators

/-- A bivariate coefficient table. -/
abbrev BivariateSeries := Nat -> Nat -> Int

/-- The empty word and all eight nonempty admissible words whose frozen
bookkeeping degree has total degree at most five. -/
def wordsThroughFive : List Word :=
  [none,
    some .single,
    some (.skip .single),
    some (.skip (.skip .single)),
    some (.take .single),
    some (.skip (.skip (.skip .single))),
    some (.take (.skip .single)),
    some (.skip (.take .single)),
    some (.skip (.skip (.skip (.skip .single))))]

/-- The admissible golden-word coefficient table through total degree five.

Its coefficients are computed from the canonical `wordDegree`, rather than
entered as a separate exponent table. -/
def goldenPrefix : BivariateSeries := fun a b =>
  ((wordsThroughFive.map wordDegree).count (a, b) : Nat)

/-- Coefficient table of the monomial `u^a * v^b`. -/
def monomial (a b : Nat) : BivariateSeries := fun i j =>
  if (i, j) = (a, b) then 1 else 0

/-- Coefficient table of `1 - u^a * v^b`, for a nonconstant monomial. -/
def oneMinusMonomial (a b : Nat) : BivariateSeries := fun i j =>
  if (i, j) = (0, 0) then 1
  else if (i, j) = (a, b) then -1 else 0

/-- Cauchy multiplication of bivariate coefficient tables. -/
def convolution (f g : BivariateSeries) : BivariateSeries := fun a b =>
  ∑ i ∈ range (a + 1),
    ∑ j ∈ range (b + 1), f i j * g (a - i) (b - j)

/-- Finite multiplication of bivariate coefficient tables. -/
def multiplyAll : List BivariateSeries -> BivariateSeries
  | [] => monomial 0 0
  | factor :: factors => convolution factor (multiplyAll factors)

/-- Factors with positive Witt exponent through total degree five. -/
def positiveWittFactors : BivariateSeries :=
  multiplyAll
    [oneMinusMonomial 1 0, oneMinusMonomial 0 1,
      oneMinusMonomial 2 1, oneMinusMonomial 1 2,
      oneMinusMonomial 4 1, oneMinusMonomial 3 2,
      oneMinusMonomial 2 3]

/-- Factors with negative Witt exponent through total degree five. -/
def negativeWittFactors : BivariateSeries :=
  multiplyAll
    [oneMinusMonomial 2 0, oneMinusMonomial 0 2,
      oneMinusMonomial 3 1, oneMinusMonomial 2 2]

set_option maxHeartbeats 2000000 in
private theorem degree_five_grid_computation :
    forall a b : Fin 6, (a : Nat) + (b : Nat) <= 5 ->
      convolution goldenPrefix positiveWittFactors a b =
        negativeWittFactors a b := by
  decide

/-- **Golden cyclotomic table through total degree five.** After clearing the
positive-exponent Euler factors, the golden word prefix agrees coefficientwise
with the negative-exponent factors in every bidegree `a + b <= 5`.

Thus the positive entries are
`e10 = e01 = e21 = e12 = e41 = e32 = e23 = 1`, the negative entries are
`e20 = e02 = e31 = e22 = -1`, and every omitted entry through total degree
five is zero.  This is an exact finite formal identity; it makes no analytic
claim about convergence of the resulting infinite zeta cascade. -/
theorem golden_cyclotomic_table_degree_five :
    forall a b : Nat, a + b <= 5 ->
      convolution goldenPrefix positiveWittFactors a b =
        negativeWittFactors a b := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  intro a b hab
  have ha : a < 6 := by omega
  have hb : b < 6 := by omega
  exact degree_five_grid_computation ⟨a, ha⟩ ⟨b, hb⟩ hab

#print axioms golden_cyclotomic_table_degree_five

end D5.S1.Recurrence.Witt.GoldenCyclotomicTable
