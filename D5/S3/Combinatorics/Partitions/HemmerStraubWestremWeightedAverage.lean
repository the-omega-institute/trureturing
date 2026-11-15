/- GID: D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The weighted Ev character average has an even binomial closed form. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#21960; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22528.
The four public definitions retain the expressions of equation (6.1).
Private coefficient owners ev_right, right_coefficient and triProd are reused
through Batteries.Tactic.OpenPrivate; their source is unchanged.
The Frobenius coefficient model is inherited from HemmerStraubWestrem;
its identification with an internal Specht-module character is not formalized.
Normalized formal ODE uniqueness applies PowerSeriesNormalizedContraction.exists_unique_fixed
and UnitReversionSquareParity.agree_mul to termwise integration of the common driver.
Every proof is bind-only after expanding the consumed helpers: partition removal
uses Nat.Partition.partitionWithPartEquiv, and the remaining steps instantiate
coefficient identities, reindex finite sums, and normalize algebraic expressions.
No escape witness is asserted; admission uses the named external problem.

Frozen declaration identities (not module pins):
F01: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction | D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
  statement_id: sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981
F02: D5/S1/Recurrence/Invariants/UnitReversionSquareParity | D5.S1.Recurrence.Invariants.UnitReversionSquareParity.Agree
  statement_id: sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34
F03: D5/S1/Recurrence/Invariants/UnitReversionSquareParity | D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_mul
  statement_id: sha256:b4802ea85bb0964fd0f4727040613a738a00c26e68db4c758612d114939c9e3a
F04: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3
  statement_id: sha256:37fbbbc487632ea4ae9e7b29262def02f95e5ee9d67dbd3b68580099edd94140
F05: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes
  statement_id: sha256:1a00bd6f47288dfab76824cc704475a7b6fb23c66f72e621fb7f72e005dd5063
F06: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar
  statement_id: sha256:8d961a5d4c7fff5a6f692b41435908f395bee0d610a4ccc6770419ba64d042fb
F07: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.result
  statement_id: sha256:7b038a7e2d0753c287105d56ea4273b6a0fc75c3bff18c86f29f1690774d7839
F08: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.Exponent
  statement_id: sha256:829f9b2dcba091642c63b32849553dc0b45fba447186e767a7eccc4ffa275aea
F09: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.exponentParts
  statement_id: sha256:98805f7e97c35c1822084b9363b8490b390476cf38a403d416f3979e953c6506
F10: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.exponentParts.eq_1
  statement_id: sha256:7b6e56bf48d77611e4945a7747ff89810df27a35fea01864ba5cacf8712c4162
F11: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.exponentParts_partitionExponent
  statement_id: sha256:c1ffb4199ba3e9504403822eb44a5ffbe291e01c3f6fe2373aeca4588b1141f6
F12: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.partitionExponent
  statement_id: sha256:e8d32bd4e8f39ae5156a46ceec34053498f8cd902840afd26049860a7ce69210
F13: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zExponent
  statement_id: sha256:1c780283b2158f88276cff717fa73140f61975baf715afa98481bcd1ff07dbc3
F14: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zExponent_add_single
  statement_id: sha256:017f94a201ebbb6daff5cfa3b0a4e569951d4498cb4c56731ba7da3824102c20
F15: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zExponent_pos
  statement_id: sha256:48c6e4d341a82d520959d4d3678067521e196cdfb9a9806ed8bbf0db67e600ec
F16: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition
  statement_id: sha256:950d49e7fa84025719dbbb066a9b05ec1c1395bce4c56fb0475381b8cbe4ae0f
F17: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2 | D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition.eq_1
  statement_id: sha256:896769bfbd00a6d307c8d28e56d2ca6527e8f4385048c4b7d6f9b37da7c3c7d3
F18: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | _private.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.0.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.altCoeff
  statement_id: sha256:472b0bf9c8f5f8d3df7a2c8e3921554c416d75063d12fb457124e62e392693b6
F19: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | _private.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.0.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.ev_right
  statement_id: sha256:de1d4aa611b320c4a8cf8d33993809f56f860fc14845a0cb47701b2c3aa53013
F20: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | _private.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.0.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.plusProd
  statement_id: sha256:9889946200238b88426feeaf834da28a1c1f399a030a2193620e4a1e1d7002b4
F21: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | _private.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.0.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.right_coefficient
  statement_id: sha256:60d91e1a5dcc23fc2db91f1fe83ede8df723c904bf357f1e690c900665ee41c9
F22: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem | _private.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.0.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.triProd
  statement_id: sha256:2c3f837dc70fbb85d36540f52fcbeaf5843afc2c734767137ec868ae96e7980a

Per-declaration classification after expanding same-delivery helpers.
proof_shape: weight: bind-only; escape_witness: none; consumers: leftAverage, rightAverage, average_equality, rightAverage_constantTerm.
Direct frozen dependencies after helper expansion (weight): F16.
proof_shape: leftAverage: bind-only; escape_witness: none; consumers: claim, average_equality, result.
Direct frozen dependencies after helper expansion (leftAverage): F04, F05, F06, F16.
proof_shape: rightAverage: bind-only; escape_witness: none; consumers: claim, average_equality, rightAverage_constantTerm, rightAverage_closed, result.
Direct frozen dependencies after helper expansion (rightAverage): F05, F06, F16.
proof_shape: claim: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies after helper expansion (claim): F04, F05, F06, F16.
proof_shape: average_equality: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies after helper expansion (average_equality): F04, F05, F06, F07, F16.
proof_shape: rectangular_sum_coefficient: bind-only; escape_witness: none; consumers: character_constantTerm.
Direct frozen dependencies after helper expansion (rectangular_sum_coefficient): F05, F06, F18, F19, F20, F21, F22.
proof_shape: partition_exponent_count: bind-only; escape_witness: none; consumers: z_partition_cons.
Direct frozen dependencies after helper expansion (partition_exponent_count): F08, F09, F10, F11, F12.
proof_shape: z_partition_cons: bind-only; escape_witness: none; consumers: cycle_term_cons.
Direct frozen dependencies after helper expansion (z_partition_cons): F08, F09, F10, F11, F12, F13, F14, F16, F17.
proof_shape: cycleTerm: bind-only; escape_witness: none; consumers: cycleAverage, cycle_term_cons, marked_cycle_sum, cycle_average_recursion, cycle_average_zero, rightAverage_constantTerm.
Direct frozen dependencies after helper expansion (cycleTerm): F16.
proof_shape: cycleAverage: bind-only; escape_witness: none; consumers: marked_cycle_sum, cycle_average_recursion, cycle_average_zero, cycle_average_derivative, cycle_generating_series, weighted_constant_term_series, rightAverage_constantTerm, rightAverage_closed.
Direct frozen dependencies after helper expansion (cycleAverage): F16.
proof_shape: cycle_term_cons: bind-only; escape_witness: none; consumers: marked_cycle_sum.
Direct frozen dependencies after helper expansion (cycle_term_cons): F08, F09, F10, F11, F12, F13, F14, F15, F16, F17.
proof_shape: marked_cycle_sum: bind-only; escape_witness: none; consumers: cycle_average_recursion.
Direct frozen dependencies after helper expansion (marked_cycle_sum): F08, F09, F10, F11, F12, F13, F14, F15, F16, F17.
proof_shape: cycle_average_recursion: bind-only; escape_witness: none; consumers: cycle_average_derivative.
Direct frozen dependencies after helper expansion (cycle_average_recursion): F08, F09, F10, F11, F12, F13, F14, F15, F16, F17.
proof_shape: cycle_average_zero: bind-only; escape_witness: none; consumers: cycle_generating_series.
Direct frozen dependencies after helper expansion (cycle_average_zero): F08, F12, F16.
proof_shape: cycle_average_derivative: bind-only; escape_witness: none; consumers: cycle_generating_series.
Direct frozen dependencies after helper expansion (cycle_average_derivative): F08, F09, F10, F11, F12, F13, F14, F15, F16, F17.
proof_shape: power_series_ode_unique: bind-only; escape_witness: none; consumers: cycle_generating_series.
Direct frozen dependencies after helper expansion (power_series_ode_unique): F01, F02, F03.
proof_shape: square_series: bind-only; escape_witness: none; consumers: constant_term_cancellation.
Direct frozen dependencies after helper expansion (square_series): none.
proof_shape: consecutive_series: bind-only; escape_witness: none; consumers: constant_term_cancellation.
Direct frozen dependencies after helper expansion (consecutive_series): none.
proof_shape: constant_term_cancellation: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (constant_term_cancellation): none.
proof_shape: coefficient_even_cube: bind-only; escape_witness: none; consumers: rightAverage_closed.
Direct frozen dependencies after helper expansion (coefficient_even_cube): none.
proof_shape: geometric_square: bind-only; escape_witness: none; consumers: geometricSquare_derivative.
Direct frozen dependencies after helper expansion (geometric_square): none.
proof_shape: coeff_geometric: bind-only; escape_witness: none; consumers: geometric_derivative, three_square_derivative.
Direct frozen dependencies after helper expansion (coeff_geometric): none.
proof_shape: coeff_geometricSquare: bind-only; escape_witness: none; consumers: geometric_derivative, pair_coefficient.
Direct frozen dependencies after helper expansion (coeff_geometricSquare): none.
proof_shape: geometric_derivative: bind-only; escape_witness: none; consumers: geometricSquare_derivative.
Direct frozen dependencies after helper expansion (geometric_derivative): none.
proof_shape: geometricSquare_derivative: bind-only; escape_witness: none; consumers: three_square_derivative.
Direct frozen dependencies after helper expansion (geometricSquare_derivative): none.
proof_shape: three_square_derivative: bind-only; escape_witness: none; consumers: cycle_generating_series.
Direct frozen dependencies after helper expansion (three_square_derivative): none.
proof_shape: constantTermSeries: bind-only; escape_witness: none; consumers: constantTermSeries_sub, constantTermSeries_map_mul, constantTerm_pair, constantTerm_shift_pair, weighted_constant_term_series, rightAverage_closed.
Direct frozen dependencies after helper expansion (constantTermSeries): none.
proof_shape: constantTerm_C_mul: bind-only; escape_witness: none; consumers: constantTermSeries_map_mul, character_constantTerm.
Direct frozen dependencies after helper expansion (constantTerm_C_mul): none.
proof_shape: constantTermSeries_sub: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (constantTermSeries_sub): none.
proof_shape: constantTermSeries_map_mul: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (constantTermSeries_map_mul): none.
proof_shape: constantTerm_shift: bind-only; escape_witness: none; consumers: constantTerm_shift_pair.
Direct frozen dependencies after helper expansion (constantTerm_shift): none.
proof_shape: laurent_geometric_pair_term: bind-only; escape_witness: none; consumers: pair_coefficient.
Direct frozen dependencies after helper expansion (laurent_geometric_pair_term): none.
proof_shape: pair_coefficient: bind-only; escape_witness: none; consumers: pair_coefficient_zero, pair_coefficient_one.
Direct frozen dependencies after helper expansion (pair_coefficient): none.
proof_shape: pair_coefficient_zero: bind-only; escape_witness: none; consumers: constantTerm_pair.
Direct frozen dependencies after helper expansion (pair_coefficient_zero): none.
proof_shape: pair_coefficient_one: bind-only; escape_witness: none; consumers: constantTerm_shift_pair.
Direct frozen dependencies after helper expansion (pair_coefficient_one): none.
proof_shape: constantTerm_pair: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (constantTerm_pair): none.
proof_shape: constantTerm_shift_pair: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (constantTerm_shift_pair): none.
proof_shape: cycleInput: bind-only; escape_witness: none; consumers: cycle_generating_series, weighted_constant_term_series, cycleInput_product, character_constantTerm, rightAverage_constantTerm, rightAverage_closed.
Direct frozen dependencies after helper expansion (cycleInput): none.
proof_shape: cycle_generating_series: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (cycle_generating_series): F01, F02, F03, F08, F09, F10, F11, F12, F13, F14, F15, F16, F17.
proof_shape: geometricSquare_one: bind-only; escape_witness: none; consumers: weighted_constant_term_series.
Direct frozen dependencies after helper expansion (geometricSquare_one): none.
proof_shape: weighted_constant_term_series: bind-only; escape_witness: none; consumers: rightAverage_closed.
Direct frozen dependencies after helper expansion (weighted_constant_term_series): F01, F02, F03, F08, F09, F10, F11, F12, F13, F14, F15, F16, F17.
proof_shape: laurent_coefficient_nat: bind-only; escape_witness: none; consumers: constantTerm_polynomial_shift.
Direct frozen dependencies after helper expansion (laurent_coefficient_nat): none.
proof_shape: constantTerm_polynomial_shift: bind-only; escape_witness: none; consumers: constantTerm_polynomial_difference.
Direct frozen dependencies after helper expansion (constantTerm_polynomial_shift): none.
proof_shape: constantTerm_polynomial_difference: bind-only; escape_witness: none; consumers: character_constantTerm.
Direct frozen dependencies after helper expansion (constantTerm_polynomial_difference): none.
proof_shape: laurent_trinomial: bind-only; escape_witness: none; consumers: laurent_product.
Direct frozen dependencies after helper expansion (laurent_trinomial): none.
proof_shape: laurent_product: bind-only; escape_witness: none; consumers: cycleInput_product.
Direct frozen dependencies after helper expansion (laurent_product): F22.
proof_shape: cycleInput_product: bind-only; escape_witness: none; consumers: character_constantTerm.
Direct frozen dependencies after helper expansion (cycleInput_product): F22.
proof_shape: character_constantTerm: bind-only; escape_witness: none; consumers: rightAverage_constantTerm.
Direct frozen dependencies after helper expansion (character_constantTerm): F05, F06, F18, F19, F20, F21, F22.
proof_shape: rightAverage_constantTerm: bind-only; escape_witness: none; consumers: rightAverage_closed.
Direct frozen dependencies after helper expansion (rightAverage_constantTerm): F05, F06, F16, F18, F19, F20, F21, F22.
proof_shape: rightAverage_closed: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies after helper expansion (rightAverage_closed): F01, F02, F03, F05, F06, F08, F09, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22.
proof_shape: result: bind-only; escape_witness: none; consumers: external open-problem result.
Direct frozen dependencies after helper expansion (result): F01, F02, F03, F04, F05, F06, F07, F08, F09, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22.
-/

import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

open scoped BigOperators
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

/-- The reciprocal of the source's centralizer factor
`z_λ = ∏ j = 1, ..., n, j^(m_j) * m_j!`.
The existing `zPartition` uses the multiplicities of positive part sizes. -/
def weight {n : ℕ} (lam : Nat.Partition n) : ℚ :=
  (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹

/-- The signed, even-three-row weighted average in equation (6.1). -/
def leftAverage (n : ℕ) : ℚ :=
  ∑ lam : Nat.Partition n, weight lam *
    ((((evTypes lam.parts.toList).map fun τ =>
      ∑ μ ∈ R3 (2 * n), (-1 : ℤ) ^ τ.length * frobChar μ τ).sum : ℤ) : ℚ)

/-- The rectangular-character weighted average in equation (6.1). -/
def rightAverage (n : ℕ) : ℚ :=
  ∑ lam : Nat.Partition n, weight lam *
    ((((evTypes lam.parts.toList).map fun τ => frobChar ![n, n, 0] τ).sum : ℤ) : ℚ)

/-- Journal Conjecture 17 (arXiv v1 Conjecture 6.1): both equalities,
for every positive integer n, with the even/odd closed form. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    leftAverage n = rightAverage n ∧
      rightAverage n = if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open scoped BigOperators

private theorem average_equality (n : ℕ) (hn : 1 ≤ n) :
    leftAverage n = rightAverage n := by
  apply Finset.sum_congr rfl
  intro lam _
  rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.result n hn lam]

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

open private right_coefficient ev_right triProd
  from D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
private theorem rectangular_sum_coefficient (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) :
    ((evTypes p.parts.toList).map fun τ => frobChar ![n, n, 0] τ).sum =
      (2 : ℤ) ^ p.parts.card *
        ((triProd p.parts.toList).coeff n - (triProd p.parts.toList).coeff (n + 1)) := by
  have hsum : p.parts.toList.sum = n := by simpa using p.parts_sum
  have hpos : ∀ a ∈ p.parts.toList, 0 < a := by
    intro a ha
    exact p.parts_pos (by simpa using ha)
  have h := right_coefficient p.parts.toList (by omega) hpos
  rw [← ev_right] at h
  simpa only [hsum, Multiset.length_toList] using h
end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

private theorem partition_exponent_count {n : ℕ} (p : Nat.Partition n)
    (k : ℕ) (hk : 0 < k) : partitionExponent p (k - 1) = p.parts.count k := by
  have h := congrArg (Multiset.count k) (exponentParts_partitionExponent p)
  rw [exponentParts, show k = Nat.succ (k - 1) by omega,
    Multiset.count_map_eq_count' Nat.succ _ Nat.succ_injective,
    Finsupp.count_toMultiset] at h
  simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using h

private theorem z_partition_cons {n m k : ℕ}
    (p : Nat.Partition n) (q : Nat.Partition m)
    (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
    zPartition p = k * (q.parts.count k + 1) * zPartition q := by
  have he : partitionExponent p = partitionExponent q + Finsupp.single (k - 1) 1 := by
    simp only [partitionExponent, hp, Multiset.map_cons]
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]
    exact add_comm _ _
  rw [zPartition, he, zExponent_add_single, partition_exponent_count q k hk]
  congr 2
  omega

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private def cycleTerm (a : ℕ → R) {n : ℕ} (p : Nat.Partition n) : R :=
  (zPartition p : ℚ)⁻¹ • (p.parts.map a).prod

private def cycleAverage (a : ℕ → R) (n : ℕ) : R :=
  ∑ p : Nat.Partition n, cycleTerm a p

private theorem cycle_term_cons (a : ℕ → R) {n m k : ℕ}
    (p : Nat.Partition n) (q : Nat.Partition m)
    (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
    ((k : ℚ) * (q.parts.count k + 1)) • cycleTerm a p = a k * cycleTerm a q := by
  have hz : (zPartition q : ℚ) ≠ 0 := by
    exact_mod_cast (zExponent_pos (partitionExponent q)).ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : (q.parts.count k + 1 : ℚ) ≠ 0 := by
    exact Nat.cast_add_one_ne_zero (Multiset.count k q.parts)
  have hs : ((k : ℚ) * (q.parts.count k + 1)) * (zPartition p : ℚ)⁻¹ =
      (zPartition q : ℚ)⁻¹ := by
    rw [z_partition_cons p q hk hp]
    push_cast
    field_simp
  simp only [cycleTerm, hp, Multiset.map_cons, Multiset.prod_cons, smul_smul, hs]
  exact (mul_smul_comm _ _ _).symm


private theorem marked_cycle_sum (a : ℕ → R) (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    (∑ p : Nat.Partition n, ((k : ℚ) * p.parts.count k) • cycleTerm a p) =
      a k * cycleAverage a (n - k) := by
  let e := Nat.Partition.partitionWithPartEquiv hk hkn
  calc
    _ = ∑ p : {p : Nat.Partition n // k ∈ p.parts},
        ((k : ℚ) * p.val.parts.count k) • cycleTerm a p.val := by
      apply Finset.sum_congr_set {p : Nat.Partition n | k ∈ p.parts}
      · intro p hp
        rfl
      · intro p hp
        simp [Multiset.count_eq_zero_of_notMem hp]
    _ = ∑ q : Nat.Partition (n - k), a k * cycleTerm a q := by
      apply Fintype.sum_equiv e
      intro p
      have hp : p.val.parts = k ::ₘ (e p).parts := by
        dsimp [e]
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
        exact (Multiset.cons_erase p.property).symm
      have hc : p.val.parts.count k = (e p).parts.count k + 1 := by
        rw [hp]
        simp
      rw [hc, Nat.cast_add, Nat.cast_one]
      exact cycle_term_cons a p.val (e p) hk hp
    _ = _ := by rw [cycleAverage, Finset.mul_sum]

private theorem cycle_average_recursion (a : ℕ → R) (n : ℕ) :
    (n : ℚ) • cycleAverage a n =
      ∑ k ∈ Finset.Icc 1 n, a k * cycleAverage a (n - k) := by
  have hdeg (p : Nat.Partition n) :
      (∑ k ∈ Finset.Icc 1 n, k * p.parts.count k) = n := by
    calc
      _ = ∑ k ∈ p.parts.toFinset, p.parts.count k * k := by
        symm
        calc
          _ = ∑ k ∈ p.parts.toFinset, k * p.parts.count k := by
            apply Finset.sum_congr rfl
            intro k _
            exact mul_comm _ _
          _ = _ := by
            apply Finset.sum_subset
            · intro k hk
              have hk' := Multiset.mem_toFinset.mp hk
              exact Finset.mem_Icc.mpr ⟨p.parts_pos hk', p.le_of_mem_parts hk'⟩
            · intro k hk hnot
              simp [Multiset.count_eq_zero_of_notMem (by simpa using hnot)]
      _ = n := by
        simpa only [nsmul_eq_mul, id_eq, Multiset.map_id, Multiset.map_id', Nat.cast_id,
          p.parts_sum] using
          (Finset.sum_multiset_map_count p.parts id).symm
  calc
    _ = ∑ p : Nat.Partition n, ∑ k ∈ Finset.Icc 1 n,
        ((k : ℚ) * p.parts.count k) • cycleTerm a p := by
      rw [cycleAverage, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_smul]
      congr 1
      exact_mod_cast (hdeg p).symm
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n,
        ((k : ℚ) * p.parts.count k) • cycleTerm a p := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hk, hkn⟩ := Finset.mem_Icc.mp hk
      exact marked_cycle_sum a n k hk hkn

private theorem cycle_average_zero (a : ℕ → R) : cycleAverage a 0 = 1 := by
  simp [cycleAverage, cycleTerm, zPartition, partitionExponent, zExponent]

private theorem cycle_average_derivative (a : ℕ → R) :
    PowerSeries.derivative (PowerSeries.mk (cycleAverage a)) =
      (PowerSeries.mk fun k => a (k + 1)) * PowerSeries.mk (cycleAverage a) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  rw [show cycleAverage a (n + 1) * (n + 1 : R) =
      ((n + 1 : ℕ) : ℚ) • cycleAverage a (n + 1) by simp [Algebra.smul_def, mul_comm]]
  rw [cycle_average_recursion]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2 <;> omega

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity

private theorem power_series_ode_unique {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : PowerSeries R) {f g : PowerSeries R}
    (hf0 : constantCoeff f = 1) (hg0 : constantCoeff g = 1)
    (hf : derivative f = f * a) (hg : derivative g = g * a) : f = g := by
  let step (h : PowerSeries R) : PowerSeries R :=
    1 + X * mk (fun n => (n + 1 : ℚ)⁻¹ • coeff n (h * a))
  have hstep0 (h : PowerSeries R) (_ : constantCoeff h = 1) :
      constantCoeff (step h) = 1 := by simp [step]
  have hcontract {d : ℕ} {h k : PowerSeries R} (_ : 1 ≤ d)
      (_ : constantCoeff h = 1) (_ : constantCoeff k = 1) (hhk : Agree d h k) :
      Agree (d + 1) (step h) (step k) := by
    intro n hn
    cases n with
    | zero => simp [step]
    | succ n =>
      simp only [step, map_add, coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, coeff_succ_X_mul, coeff_mk, zero_add]
      exact congrArg ((n + 1 : ℚ)⁻¹ • ·)
        (agree_mul hhk (fun _ _ => rfl) n (by omega))
  have hfixed (h : PowerSeries R) (h0 : constantCoeff h = 1)
      (hD : derivative h = h * a) : h = step h := by
    ext n
    cases n with
    | zero => simpa [step] using h0
    | succ n =>
      simp only [step, map_add, coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, coeff_succ_X_mul, coeff_mk, zero_add]
      have he := congrArg (coeff n) hD
      rw [coeff_derivative] at he
      rw [← he, show coeff (n + 1) h * (n + 1 : R) =
        (n + 1 : ℚ) • coeff (n + 1) h by simp [Algebra.smul_def, mul_comm],
        smul_smul, inv_mul_cancel₀ (by positivity : (n + 1 : ℚ) ≠ 0), one_smul]

  obtain ⟨u, _, _, hu⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      step hstep0 (fun hd h0 k0 hhk => hcontract hd h0 k0 hhk)
  exact (hu f hf0 (hfixed f hf0 hf)).trans (hu g hg0 (hfixed g hg0 hg)).symm

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries

private theorem square_series :
    (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2) =
      2 * (invOneSubPow ℚ 3).val - (invOneSubPow ℚ 2).val := by
  ext n
  simp only [invOneSubPow, coeff_mk, map_sub, mul_comm (2 : PowerSeries ℚ),
    coeff_mul_ofNat]
  simp only [Nat.cast_choose_two, Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem consecutive_series :
    (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)) =
      2 * (invOneSubPow ℚ 3).val := by
  ext n
  simp only [invOneSubPow, coeff_mk, mul_comm (2 : PowerSeries ℚ), coeff_mul_ofNat]
  simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem constant_term_cancellation :
    (invOneSubPow ℚ 2).val *
      ((expand 2 (by decide) (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2)) -
        X * (expand 2 (by decide)
          (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)))) =
      expand 2 (by decide) (invOneSubPow ℚ 3).val := by
  have hrel : (1 - X : PowerSeries ℚ) * (invOneSubPow ℚ 3).val =
      (invOneSubPow ℚ 2).val := by
    simpa using one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ 2 1
  have he := congrArg (expand 2 (by decide)) hrel
  simp only [map_mul, map_sub, map_one, expand_X] at he
  rw [square_series, consecutive_series, map_sub, map_mul, map_ofNat]
  calc
    _ = (invOneSubPow ℚ 2).val *
        ((1 - X) ^ 2 * expand 2 (by decide) (invOneSubPow ℚ 3).val) := by
      rw [← he]
      ring
    _ = _ := by
      rw [← mul_assoc, show (invOneSubPow ℚ 2).val * (1 - X) ^ 2 = 1 from (invOneSubPow ℚ
        2).val_inv, one_mul]

private theorem coefficient_even_cube (n : ℕ) :
    (expand 2 (by decide) (invOneSubPow ℚ 3).val).coeff n =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  rw [coeff_expand]
  simp only [invOneSubPow, coeff_mk, Nat.add_comm 2, even_iff_two_dvd]

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries
variable {R : Type*} [CommRing R]



private theorem geometric_square (r : R) : (rescale r (invOneSubPow _ 1).val) ^ 2 = (rescale r
  (invOneSubPow _ 2).val) := by
  rw [← map_pow]
  congr 1
  simpa [pow_two, invOneSubPow_add, Units.val_mul] using
    (congrArg Units.val (invOneSubPow_add R 1 1)).symm

private theorem coeff_geometric (r : R) (n : ℕ) : coeff n ((rescale r (invOneSubPow _ 1).val)) =
  r ^ n := by
  simp [coeff_rescale, invOneSubPow]

private theorem coeff_geometricSquare (r : R) (n : ℕ) :
    coeff n ((rescale r (invOneSubPow _ 2).val)) = r ^ n * (n + 1) := by
  simp [coeff_rescale, invOneSubPow, Nat.add_comm]

private theorem geometric_derivative (r : R) :
    derivative ((rescale r (invOneSubPow _ 1).val)) = C r * (rescale r (invOneSubPow _ 2).val)
      := by
  ext n
  simp only [coeff_derivative, coeff_geometric, coeff_C_mul, coeff_geometricSquare,
    pow_succ]
  ring

private theorem geometricSquare_derivative (r : R) :
    derivative ((rescale r (invOneSubPow _ 2).val)) =
      (rescale r (invOneSubPow _ 2).val) * (C (2 * r) * (rescale r (invOneSubPow _ 1).val)) := by
  rw [← geometric_square, derivative_pow, geometric_derivative, ← geometric_square]
  norm_num
  simp only [map_ofNat]
  ring

private theorem three_square_derivative (r s t : R) :
    derivative ((rescale r (invOneSubPow _ 2).val) * (rescale s (invOneSubPow _ 2).val) *
      (rescale t (invOneSubPow _ 2).val)) =
      ((rescale r (invOneSubPow _ 2).val) * (rescale s (invOneSubPow _ 2).val) * (rescale t
        (invOneSubPow _ 2).val)) *
        PowerSeries.mk (fun k => 2 * (r ^ (k + 1) + s ^ (k + 1) + t ^ (k + 1))) := by
  have he : PowerSeries.mk (fun k => 2 * (r ^ (k + 1) + s ^ (k + 1) + t ^ (k + 1))) =
      C (2 * r) * (rescale r (invOneSubPow _ 1).val) + C (2 * s) * (rescale s (invOneSubPow _
        1).val) + C (2 * t) * (rescale t (invOneSubPow _ 1).val) := by
    ext n
    simp only [coeff_mk, map_add, coeff_C_mul, coeff_geometric, pow_succ]
    ring
  rw [he, derivative.leibniz, derivative.leibniz]
  simp only [smul_eq_mul, geometricSquare_derivative]
  ring

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries


private def constantTermSeries (f : PowerSeries (LaurentPolynomial ℚ)) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv
    ℚ).toLinearMap) (PowerSeries.coeff n f)

private theorem constantTerm_C_mul (a : ℚ) (f : (LaurentPolynomial ℚ)) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
      (LaurentPolynomial.C a * f) = a * ((Finsupp.lapply (R := ℚ) 0).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) f := by
  exact AddMonoidAlgebra.coeff_single_zero_mul f a 0

private theorem constantTermSeries_sub (f g : PowerSeries (LaurentPolynomial ℚ)) :
    constantTermSeries (f - g) = constantTermSeries f - constantTermSeries g := by
  ext n
  simp [constantTermSeries]

private theorem constantTermSeries_map_mul (f : PowerSeries ℚ) (g : PowerSeries
  (LaurentPolynomial ℚ)) :
    constantTermSeries ((PowerSeries.map LaurentPolynomial.C f) * g) =
      f * constantTermSeries g := by
  ext n
  simp only [constantTermSeries, coeff_mk, coeff_mul, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact constantTerm_C_mul _ _

private theorem constantTerm_shift (f : (LaurentPolynomial ℚ)) (k : ℤ) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
      (LaurentPolynomial.T k * f) = f.coeff (-k) := by
  change (LaurentPolynomial.T k * f).coeff 0 = _
  simpa only [zero_sub, add_zero, one_mul, LaurentPolynomial.T] using
    AddMonoidAlgebra.coeff_single_mul_apply f (1 : ℚ) k (0 : ℤ)


private theorem laurent_geometric_pair_term (i j : ℕ) :
    (LaurentPolynomial.T (1 : ℤ) ^ i * (i + 1 : (LaurentPolynomial ℚ))) *
      (LaurentPolynomial.T (-1 : ℤ) ^ j * (j + 1 : (LaurentPolynomial ℚ))) =
      LaurentPolynomial.C ((i + 1 : ℚ) * (j + 1 : ℚ)) *
        LaurentPolynomial.T ((i : ℤ) - j) := by
  simp only [LaurentPolynomial.T_pow, mul_one, mul_neg_one]
  rw [map_mul]
  have hi : (i + 1 : (LaurentPolynomial ℚ)) = LaurentPolynomial.C (i + 1 : ℚ) := by simp
  have hj : (j + 1 : (LaurentPolynomial ℚ)) = LaurentPolynomial.C (j + 1 : ℚ) := by simp
  rw [hi, hj, sub_eq_add_neg, LaurentPolynomial.T_add]
  ring

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries

private theorem pair_coefficient (n : ℕ) (e : ℤ) :
    (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff e =
      ∑ i ∈ Finset.range (n + 1),
        if (i : ℤ) - (n - i : ℕ) = e then
          (i + 1 : ℚ) * (((n - i : ℕ) : ℚ) + 1) else 0 := by
  let c : (LaurentPolynomial ℚ) →ₗ[ℚ] ℚ := {
    toFun := fun p => p.coeff e
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  change c _ = _
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_geometricSquare, coeff_geometricSquare, laurent_geometric_pair_term]
  change (LaurentPolynomial.C _ * LaurentPolynomial.T _).coeff e = _
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

private theorem pair_coefficient_zero (n : ℕ) :
    (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff 0 =
      if Even n then (((n / 2 : ℕ) : ℚ) + 1) ^ 2 else 0 := by
  rw [pair_coefficient]
  split_ifs with hn
  · have he : n % 2 = 0 := Nat.even_iff.mp hn
    rw [Finset.sum_eq_single (n / 2)]
    · have hnat : n - n / 2 = n / 2 := by omega
      simp [hnat, pow_two]
    · intro b hb hne
      have hb' := Finset.mem_range.mp hb
      have hne' : (b : ℤ) - (n - b : ℕ) ≠ 0 := by omega
      simp [hne']
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
    have hne : (i : ℤ) - (n - i : ℕ) ≠ 0 := by omega
    simp [hne]

private theorem pair_coefficient_one (n : ℕ) :
    (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff 1 =
      if Even n then 0 else (((n / 2 : ℕ) : ℚ) + 1) * (((n / 2 : ℕ) : ℚ) + 2) := by
  rw [pair_coefficient]
  split_ifs with hn
  · apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : n % 2 = 0 := Nat.even_iff.mp hn
    have hne : (i : ℤ) - (n - i : ℕ) ≠ 1 := by omega
    simp [hne]
  · have he : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
    rw [Finset.sum_eq_single (n / 2 + 1)]
    · have hnat : n - (n / 2 + 1) = n / 2 := by omega
      have heq : ((n / 2 + 1 : ℕ) : ℤ) - (n - (n / 2 + 1) : ℕ) = 1 := by omega
      rw [ite_eq_left heq, hnat]
      push_cast
      ring
    · intro b hb hne
      have hb' := Finset.mem_range.mp hb
      have hne' : (b : ℤ) - (n - b : ℕ) ≠ 1 := by omega
      simp [hne']
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

private theorem constantTerm_pair :
    constantTermSeries ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ))
      (invOneSubPow _ 2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val)) =
      expand 2 (by decide) (mk fun j => (j + 1 : ℚ) ^ 2) := by
  ext n
  simp only [constantTermSeries, coeff_mk]
  change (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow
    _ 2).val) *
    (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val))).coeff 0 = _
  simpa only [coeff_expand, coeff_mk, ← even_iff_two_dvd] using pair_coefficient_zero n

private theorem constantTerm_shift_pair :
    constantTermSeries (C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) *
      ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val))) =
      X * expand 2 (by decide) (mk fun j => (j + 1 : ℚ) * (j + 2 : ℚ)) := by
  ext n
  simp only [constantTermSeries, coeff_mk, coeff_C_mul, constantTerm_shift, neg_neg]
  rw [pair_coefficient_one]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_expand, coeff_mk]
    by_cases he : Even n
    · have ho : ¬ Even (n + 1) := by rw [Nat.even_iff] at he ⊢; omega
      have hdiv : (n + 1) / 2 = n / 2 := by have := Nat.even_iff.mp he; omega
      simp [he, ho, hdiv, ← even_iff_two_dvd]
    · have ho : Even (n + 1) := Nat.even_add_one.mpr he
      simp [he, ho, ← even_iff_two_dvd]

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries

private def cycleInput (k : ℕ) : (LaurentPolynomial ℚ) :=
  2 * (LaurentPolynomial.T k + 1 + LaurentPolynomial.T (-(k : ℤ)))

private theorem cycle_generating_series :
    PowerSeries.mk (cycleAverage cycleInput) =
      (rescale (1 : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val)
          := by
  apply power_series_ode_unique (PowerSeries.mk fun k => cycleInput (k + 1))
  · simp only [constantCoeff_mk, cycle_average_zero]
  · simp only [map_mul]
    simp [← coeff_zero_eq_constantCoeff, invOneSubPow]
  · simpa only [mul_comm] using cycle_average_derivative cycleInput
  · have h := three_square_derivative (1 : (LaurentPolynomial ℚ))
      (LaurentPolynomial.T (1 : ℤ)) (LaurentPolynomial.T (-1 : ℤ))
    simpa only [cycleInput, one_pow, LaurentPolynomial.T_pow, mul_one, mul_neg_one,
      add_comm, add_left_comm, Nat.cast_add, Nat.cast_one] using h

private theorem geometricSquare_one :
    (rescale (1 : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) =
      PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val := by
  ext n
  simp [invOneSubPow, Nat.add_comm]

private theorem weighted_constant_term_series :
    constantTermSeries ((1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
      PowerSeries.mk (cycleAverage cycleInput)) =
      expand 2 (by decide) (invOneSubPow ℚ 3).val := by
  rw [cycle_generating_series, geometricSquare_one]
  have he :
      (1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
        (PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val *
          (rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
          (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
            2).val)) =
      PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val *
        (((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
          (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
            2).val)) -
          C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) *
            ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
              2).val) *
              (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
                2).val))) := by ring
  rw [he, constantTermSeries_map_mul, constantTermSeries_sub,
    constantTerm_pair, constantTerm_shift_pair]
  exact constant_term_cancellation

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
open PowerSeries
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

private theorem laurent_coefficient_nat (P : Polynomial ℚ) (n : ℕ) :
    P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => Int.natCast_inj.mp h)
    P.toFinsupp.coeff n

private theorem constantTerm_polynomial_shift (P : Polynomial ℚ) (n : ℕ) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
      (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) = P.coeff n := by
  change (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))).coeff 0 = _
  simpa only [LaurentPolynomial.T, zero_sub, neg_neg, zero_add, mul_one,
    laurent_coefficient_nat] using
    AddMonoidAlgebra.coeff_mul_single_apply P.toLaurent (1 : ℚ) (-(n : ℤ)) (0 : ℤ)


private theorem constantTerm_polynomial_difference (P : Polynomial ℚ) (n : ℕ) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
      LaurentPolynomial.T (-1 : ℤ)) *
      (P.toLaurent * LaurentPolynomial.T (-(n : ℤ)))) =
      P.coeff n - P.coeff (n + 1) := by
  rw [sub_mul, one_mul, map_sub, constantTerm_polynomial_shift]
  have he : LaurentPolynomial.T (-1 : ℤ) *
      (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) =
      P.toLaurent * LaurentPolynomial.T (-((n + 1 : ℕ) : ℤ)) := by
    rw [mul_left_comm, ← LaurentPolynomial.T_add]
    congr 2
    push_cast
    ring
  rw [he, constantTerm_polynomial_shift]

private theorem laurent_trinomial (a : ℕ) :
    Polynomial.toLaurent (Polynomial.X ^ (2 * a) + Polynomial.X ^ a + 1 : Polynomial ℚ) *
      LaurentPolynomial.T (-(a : ℤ)) =
      LaurentPolynomial.T (a : ℤ) + 1 + LaurentPolynomial.T (-(a : ℤ)) := by
  simp only [map_add, Polynomial.toLaurent_X_pow, map_one, add_mul, one_mul,
    ← LaurentPolynomial.T_add]
  have h2 : (2 : ℤ) * a + -(a : ℤ) = (a : ℤ) := by omega
  simp only [Nat.cast_mul, Nat.cast_ofNat, h2, add_neg_cancel, LaurentPolynomial.T_zero]

private theorem laurent_product (l : List ℕ) :
    (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) + 1 +
      LaurentPolynomial.T (-(a : ℤ)) : List (LaurentPolynomial ℚ)).prod =
      ((triProd l).map (Int.castRingHom ℚ)).toLaurent *
        LaurentPolynomial.T (-((l.sum : ℕ) : ℤ)) := by
  induction l with
  | nil => simp [triProd]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, triProd, Polynomial.map_mul, map_mul,
      Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      Nat.cast_add, neg_add] at ih ⊢
    rw [← laurent_trinomial a, ih, LaurentPolynomial.T_add]
    ring

private theorem cycleInput_product (l : List ℕ) :
    (l.map cycleInput).prod =
      LaurentPolynomial.C ((2 : ℚ) ^ l.length) *
        (((triProd l).map (Int.castRingHom ℚ)).toLaurent *
          LaurentPolynomial.T (-((l.sum : ℕ) : ℤ))) := by
  have he : (l.map cycleInput).prod =
      (2 : (LaurentPolynomial ℚ)) ^ l.length * (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) +
        1 +
        LaurentPolynomial.T (-(a : ℤ))).prod := by
    change (l.map fun a : ℕ => (2 : LaurentPolynomial ℚ) *
      (LaurentPolynomial.T (a : ℤ) + 1 + LaurentPolynomial.T (-(a : ℤ)))).prod =
        (2 : LaurentPolynomial ℚ) ^ l.length *
          (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) + 1 +
            LaurentPolynomial.T (-(a : ℤ))).prod
    rw [List.prod_map_mul, List.map_const', List.prod_replicate]
  rw [he, laurent_product]
  congr 1
  exact (map_pow LaurentPolynomial.C (2 : ℚ) l.length).trans (by simp only [map_ofNat]) |>.symm

private theorem character_constantTerm (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
      LaurentPolynomial.T (-1 : ℤ)) *
      (p.parts.map cycleInput).prod) =
      ((((evTypes p.parts.toList).map fun τ => frobChar ![n, n, 0] τ).sum : ℤ) : ℚ) := by
  have he := cycleInput_product p.parts.toList
  have hsum : p.parts.toList.sum = n := by simpa using p.parts_sum
  rw [Multiset.prod_map_toList, hsum, Multiset.length_toList] at he
  rw [he, mul_left_comm, constantTerm_C_mul, constantTerm_polynomial_difference,
    rectangular_sum_coefficient n hn p]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub, Polynomial.coeff_map,
    Int.coe_castRingHom]

private theorem rightAverage_constantTerm (n : ℕ) (hn : 1 ≤ n) :
    rightAverage n = ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv
      ℚ).toLinearMap) ((1 - LaurentPolynomial.T (-1 : ℤ)) * cycleAverage cycleInput n) := by
  simp only [rightAverage, cycleAverage, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cycleTerm, mul_smul_comm, map_smul, character_constantTerm n hn p]
  rfl

private theorem rightAverage_closed (n : ℕ) (hn : 1 ≤ n) :
    rightAverage n = if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  rw [rightAverage_constantTerm n hn]
  have he := congrArg (coeff n) weighted_constant_term_series
  simp only [constantTermSeries, coeff_mk] at he
  have hc : (1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) : PowerSeries
    (LaurentPolynomial ℚ)) =
      C (1 - LaurentPolynomial.T (-1 : ℤ)) := by simp
  rw [hc, coeff_C_mul, coeff_mk, coefficient_even_cube] at he
  exact he

theorem result : D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage.claim := by
  intro n hn
  exact ⟨average_equality n hn, rightAverage_closed n hn⟩

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage
