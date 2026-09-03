/- GID: D5/S3/Weil/ZetaBridge/CanonicalZeroDataFromRiemannVonMangoldt
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/CanonicalZeroDataFromRiemannVonMangoldt
   mirror-E: none(waiver:canonical-zeta-nonvacuity-bridge)
   anchors: []
   digest: Riemann-von Mangoldt growth makes the nontrivial zeta-zero set infinite and therefore constructs an actual ZeroData inhabitant. -/

import D5.S3.Weil.ZetaBridge.RiemannVonMangoldtCountGrowth
import D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite
import D5.S3.Weil.ZetaSeam.StatementSeamClosed
import Mathlib.Tactic

/-!
# Canonical `ZeroData` from Riemann-von Mangoldt

`ZeroDataNonemptyIffInfinite` already constructs every field of `ZeroData`
from the infinitude of the nontrivial zeta-zero set.  The only remaining
semantic-nonvacuity obligation is therefore infinitude.

This node proves the exact missing bridge.  A Riemann-von Mangoldt estimate for
the repository's canonical `zetaZeroConfig` forces its dyadic counts to tend
to infinity.  A finite carrier would bound every such count by the total
multiplicity of the carrier, a contradiction.  The existing equivalence then
supplies an actual `ZeroData` inhabitant.

The final input is still explicit: this module does not itself prove the
canonical Riemann-von Mangoldt estimate.  Once the hypothesis-free RvM theorem
is ported, the definitions below become an unconditional canonical witness by
specialization.
-/

/- Library-first audit trail (2026-09-03):
   * `ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite` already owns
     the duplicate-free enumeration, analytic multiplicity, symmetries, and
     finite spectral balls.  None of those fields is reconstructed here.
   * `StatementSeamClosed.zetaZeroConfig` is the hypothesis-free canonical
     set-level zero configuration of Mathlib's zeta zeros.
   * `RiemannVonMangoldtCountGrowth.dyadic_zero_count_tendsto_atTop` supplies
     the only analytic growth implication needed here.
   * The remaining proof is finite-set bookkeeping: a window sum is bounded
     by the total multiplicity on a finite carrier.
   * Repository searches found no public theorem constructing `ZeroData` from
     canonical Riemann-von Mangoldt growth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped BigOperators

namespace D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt

open Zeta23
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.RiemannVonMangoldtCountGrowth
open D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite

/-- If a zero configuration has finite carrier, all of its dyadic
multiplicity counts are bounded by the total carrier multiplicity. -/
theorem dyadic_zero_count_bounded_of_finite_carrier
    (Z : ZeroConfig) (hfinite : Z.carrier.Finite) :
    ∃ M : ℕ, ∀ T : ℝ, Z.N T (2 * T) ≤ M := by
  let M : ℕ := ∑ rho in hfinite.toFinset, Z.mult rho
  refine ⟨M, ?_⟩
  intro T
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ (Z.finite_window T (2 * T))]
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  rw [Set.Finite.mem_toFinset] at hrho ⊢
  exact hrho.1

/-- A dyadic zero count tending to infinity forces the underlying zero
carrier to be infinite. -/
theorem zeroConfig_carrier_infinite_of_dyadic_count_tendsto
    (Z : ZeroConfig)
    (hcount : Tendsto (fun T : ℝ => (Z.N T (2 * T) : ℝ)) atTop atTop) :
    Z.carrier.Infinite := by
  by_contra hnot
  rw [Set.not_infinite] at hnot
  obtain ⟨M, hM⟩ := dyadic_zero_count_bounded_of_finite_carrier Z hnot
  have heventually :
      ∀ᶠ T in atTop, (M : ℝ) < (Z.N T (2 * T) : ℝ) :=
    hcount.eventually_gt_atTop (M : ℝ)
  obtain ⟨T, hT⟩ := heventually.exists
  have hbound : (Z.N T (2 * T) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hM T
  exact (not_lt_of_ge hbound) hT

/-- Riemann-von Mangoldt for the canonical zeta zero configuration forces the
set of nontrivial zeta zeros used by `ZeroSum` to be infinite. -/
theorem nontrivial_zeta_zero_set_infinite_of_riemannVonMangoldt
    (hRvM : RiemannVonMangoldt zetaZeroConfig) :
    {rho : ℂ | D5.S3.Weil.ZeroSum.IsNontrivialZero rho}.Infinite := by
  have hcarrier : zetaZeroConfig.carrier.Infinite :=
    zeroConfig_carrier_infinite_of_dyadic_count_tendsto zetaZeroConfig
      (dyadic_zero_count_tendsto_atTop zetaZeroConfig hRvM)
  have hzeta23 : {rho : ℂ | Zeta23.IsNontrivialZero rho}.Infinite := by
    simpa only [zetaZeroConfig_carrier] using hcarrier
  simpa [D5.S3.Weil.ZeroSum.IsNontrivialZero, classicalZeta,
    Zeta23.IsNontrivialZero] using hzeta23

/-- The canonical Riemann-von Mangoldt estimate eliminates semantic vacuity:
`ZeroData` is genuinely inhabited. -/
theorem nonempty_zeroData_of_riemannVonMangoldt
    (hRvM : RiemannVonMangoldt zetaZeroConfig) :
    Nonempty ZeroData :=
  nonempty_zeroData_iff_infinite.mpr
    (nontrivial_zeta_zero_set_infinite_of_riemannVonMangoldt hRvM)

/-- A concrete choice-based `ZeroData` value under the canonical RvM input.
All enumerations are equivalent for the repository's permutation-invariant
zero sums; the purpose of this definition is semantic inhabitance, not a
computable ordering of zeta zeros. -/
noncomputable def zeroDataOfRiemannVonMangoldt
    (hRvM : RiemannVonMangoldt zetaZeroConfig) : ZeroData :=
  Classical.choice (nonempty_zeroData_of_riemannVonMangoldt hRvM)

/-- The chosen witness really enumerates only nontrivial zeta zeros. -/
theorem zeroDataOfRiemannVonMangoldt_isNontrivial
    (hRvM : RiemannVonMangoldt zetaZeroConfig) (n : ℕ) :
    D5.S3.Weil.ZeroSum.IsNontrivialZero
      ((zeroDataOfRiemannVonMangoldt hRvM).zero n) :=
  (zeroDataOfRiemannVonMangoldt hRvM).zero_isNontrivial n

/-- The chosen witness is exhaustive over every nontrivial zeta zero. -/
theorem zeroDataOfRiemannVonMangoldt_exhaustive
    (hRvM : RiemannVonMangoldt zetaZeroConfig) {rho : ℂ}
    (hrho : D5.S3.Weil.ZeroSum.IsNontrivialZero rho) :
    ∃ n, (zeroDataOfRiemannVonMangoldt hRvM).zero n = rho :=
  (zeroDataOfRiemannVonMangoldt hRvM).zero_exhaustive hrho

#print axioms dyadic_zero_count_bounded_of_finite_carrier
#print axioms zeroConfig_carrier_infinite_of_dyadic_count_tendsto
#print axioms nontrivial_zeta_zero_set_infinite_of_riemannVonMangoldt
#print axioms nonempty_zeroData_of_riemannVonMangoldt
#print axioms zeroDataOfRiemannVonMangoldt_isNontrivial
#print axioms zeroDataOfRiemannVonMangoldt_exhaustive

end D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt
