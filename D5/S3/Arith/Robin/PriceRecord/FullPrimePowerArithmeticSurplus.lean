/- GID: D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Full prime-power compensation by signed actual valuations on exact prime support. -/

import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Weil.Mertens.Gamma
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
For a positive integer with support exactly the primes at most the real
cutoff z, the full prime-power residual is strictly compensated by its
actual Euler truncation and signed log(n)-psi(z) inventory.

The cutoff includes p^k=z in psi. Every omitted layer is retained in the
summable residual. Above the cutoff exponent, additional copies pay their
cutoff price. Below it, the larger Euler tail pays both the missing copies
and the entire reference tail. The prime two pays the strict global scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus

open Finset
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (tail layerTail)

/-- The exact floor cutoff, including equality at a prime power. -/
def cutoffExponent (z : ℝ) (p : ℕ) : ℕ :=
  ⌊Real.log z / Real.log (p : ℝ)⌋₊

/-- Every omitted prime-power layer is retained; the outer prime set is finite.
For primes in this set the first omitted layer is at least two. -/
def fullPrimePowerResidual (z : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊z⌋₊, ∑' k : ℕ,
    if 2 ≤ k ∧ z < (p : ℝ) ^ k then (p : ℝ)⁻¹ ^ k / (k : ℝ) else 0

private def shiftedTail (q : ℝ) (b : ℕ) : ℝ :=
  ∑' r : ℕ, q ^ (r + (b + 1)) / (r + (b + 1) : ℕ)

/-- Integer-log and real-floor cutoffs agree, with BOTH power endpoints. -/
private theorem cutoff_spec {z : ℝ} (hz : 4 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    1 ≤ cutoffExponent z p ∧
      (p : ℝ) ^ cutoffExponent z p ≤ z ∧
      z < (p : ℝ) ^ (cutoffExponent z p + 1) ∧
      cutoffExponent z p = Nat.log p ⌊z⌋₊ := by
  let b := Nat.log p ⌊z⌋₊
  have hz0 : 0 < z := by linarith
  have hn : 4 ≤ ⌊z⌋₊ := Nat.le_floor hz
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb1 : 1 ≤ b := Nat.log_pos hp.one_lt (Nat.le_floor hpz)
  have hlo : (p : ℝ) ^ b ≤ z := by
    have hh := Nat.pow_log_le_self p (by omega : ⌊z⌋₊ ≠ 0)
    exact (by exact_mod_cast hh : (p : ℝ) ^ b ≤ (⌊z⌋₊ : ℝ)).trans
      (Nat.floor_le hz0.le)
  have hhi : z < (p : ℝ) ^ (b + 1) := by
    have hh : ⌊z⌋₊ + 1 ≤ p ^ (b + 1) := by
      simpa only [b, Nat.succ_eq_add_one] using
        (Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self hp.one_lt ⌊z⌋₊))
    exact (Nat.lt_floor_add_one z).trans_le (by exact_mod_cast hh)
  have hquot0 : 0 ≤ Real.log z / Real.log (p : ℝ) :=
    div_nonneg (Real.log_nonneg (by linarith)) hlp.le
  have hb : cutoffExponent z p = b := by
    apply (Nat.floor_eq_iff hquot0).mpr
    constructor
    · apply (le_div_iff₀ hlp).mpr
      simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp0 b) hlo
    · apply (div_lt_iff₀ hlp).mpr
      have hh := Real.log_lt_log hz0 hhi
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using hh
  exact ⟨by simpa [hb] using hb1, by simpa [hb] using hlo,
    by simpa [hb] using hhi, hb⟩

/-- The strict upper cutoff is equivalent to being past the exact floor.
In particular, a layer with p^k=z belongs to psi, never to the residual. -/
private theorem cutoff_lt_iff {z : ℝ} (hz : 4 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) (k : ℕ) :
    cutoffExponent z p < k ↔ z < (p : ℝ) ^ k := by
  obtain ⟨_, hlo, hhi, _⟩ := cutoff_spec hz hp hpz
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  constructor
  · intro hk
    exact hhi.trans_le (pow_le_pow_right₀ hp1 (by omega))
  · intro hk
    by_contra! h
    exact (pow_le_pow_right₀ hp1 h |>.trans hlo).not_gt hk

/-- A genuine strict estimate for the WHOLE shifted series.  Strictness uses
r=1; all other summands are compared to a summable geometric series. -/
private theorem shifted_tail_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (b : ℕ) :
    Summable (fun r : ℕ => q ^ (r + (b + 1)) / (r + (b + 1) : ℕ)) ∧
      shiftedTail q b < (q ^ (b + 1) / (b + 1 : ℕ)) / (1 - q) := by
  let A : ℝ := q ^ (b + 1) / (b + 1 : ℕ)
  let f : ℕ → ℝ := fun r => q ^ (r + (b + 1)) / (r + (b + 1) : ℕ)
  let g : ℕ → ℝ := fun r => A * q ^ r
  have hg : Summable g := (summable_geometric_of_lt_one hq0.le hq1).mul_left A
  have hf0 (r : ℕ) : 0 ≤ f r := by dsimp [f]; positivity
  have hdom (r : ℕ) : f r ≤ g r := by
    have hden : ((b + 1 : ℕ) : ℝ) ≤ (r + (b + 1) : ℕ) := by
      exact_mod_cast (show b + 1 ≤ r + (b + 1) by omega)
    calc
      f r ≤ q ^ (r + (b + 1)) / (b + 1 : ℕ) :=
        div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (by positivity) hden
      _ = g r := by dsimp [g, A]; rw [pow_add]; ring
  have hstrict : f 1 < g 1 := by
    calc
      f 1 < q ^ (1 + (b + 1)) / (b + 1 : ℕ) := by
        apply div_lt_div_of_pos_left (pow_pos hq0 _) (by positivity)
        exact_mod_cast (show b + 1 < 1 + (b + 1) by omega)
      _ = g 1 := by dsimp [g, A]; rw [pow_add]; ring
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hdom hg
  refine ⟨hf, ?_⟩
  have hh := Summable.tsum_lt_tsum hdom hstrict hf hg
  have hsumg : (∑' r, g r) = A / (1 - q) := by
    simpa only [g, div_eq_mul_inv] using
      ((hasSum_geometric_of_lt_one hq0.le hq1).mul_left A).tsum_eq
  simpa only [shiftedTail, f, hsumg, A] using hh

/-- Reindex the actual full residual. Summability is established before the
prefix/tail identity is used, so the real tsum default-zero convention cannot
silently discard an infinite tail. -/
private theorem residual_prime_eq_shift {z : ℝ} (hz : 4 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    (∑' k : ℕ, if 2 ≤ k ∧ z < (p : ℝ) ^ k then
      (p : ℝ)⁻¹ ^ k / (k : ℝ) else 0) =
        shiftedTail (p : ℝ)⁻¹ (cutoffExponent z p) := by
  let b := cutoffExponent z p
  let f : ℕ → ℝ := fun k => if 2 ≤ k ∧ z < (p : ℝ) ^ k then
    (p : ℝ)⁻¹ ^ k / (k : ℝ) else 0
  have hb1 : 1 ≤ b := (cutoff_spec hz hp hpz).1
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hi1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hshift (r : ℕ) : f (r + (b + 1)) =
      (p : ℝ)⁻¹ ^ (r + (b + 1)) / (r + (b + 1) : ℕ) := by
    have hk : cutoffExponent z p < r + (b + 1) := by dsimp [b] at *; omega
    have hcond : 2 ≤ r + (b + 1) ∧ z < (p : ℝ) ^ (r + (b + 1)) :=
      ⟨by omega, (cutoff_lt_iff hz hp hpz _).mp hk⟩
    simp only [f, if_pos hcond]
  have hshiftSummable : Summable (fun r : ℕ => f (r + (b + 1))) := by
    simpa only [hshift] using (shifted_tail_bound hi0 hi1 b).1
  have hf : Summable f := (summable_nat_add_iff (b + 1)).mp hshiftSummable
  have hprefix : ∑ k ∈ range (b + 1), f k = 0 := by
    apply sum_eq_zero
    intro k hk
    have hkb : k ≤ cutoffExponent z p := by
      have := mem_range.mp hk
      dsimp [b] at *
      omega
    have hn : ¬ z < (p : ℝ) ^ k := by
      simpa only [← cutoff_lt_iff hz hp hpz k, not_lt] using hkb
    simp [f, hn]
  have hh := hf.sum_add_tsum_nat_add (b + 1)
  rw [hprefix, zero_add] at hh
  calc
    _ = ∑' r : ℕ, f (r + (b + 1)) := hh.symm
    _ = shiftedTail (p : ℝ)⁻¹ b := tsum_congr hshift

/-- The price per additional copy of p dominates the first omitted
prime-power coefficient at the SAME cutoff z. -/
private theorem cutoff_price {z : ℝ} (hz : 4 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    (p : ℝ)⁻¹ ^ (cutoffExponent z p + 1) / (cutoffExponent z p + 1 : ℕ) <
      Real.log (p : ℝ) / (z * Real.log z) := by
  let b := cutoffExponent z p
  obtain ⟨_, _, hhi, _⟩ := cutoff_spec hz hp hpz
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : Real.log z < (b + 1 : ℕ) * Real.log (p : ℝ) := by
    simpa only [Real.log_pow] using Real.log_lt_log hz0 hhi
  have hprod : z * Real.log z <
      (p : ℝ) ^ (b + 1) * ((b + 1 : ℕ) * Real.log (p : ℝ)) :=
    (mul_lt_mul_of_pos_right hhi hlz).trans_le
      (mul_le_mul_of_nonneg_left hlog.le (pow_nonneg hp0.le _))
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (b + 1 : ℕ))
    (mul_pos hz0 hlz)).mpr
  calc
    (p : ℝ)⁻¹ ^ (b + 1) * (z * Real.log z) <
        (p : ℝ)⁻¹ ^ (b + 1) *
          ((p : ℝ) ^ (b + 1) * ((b + 1 : ℕ) * Real.log (p : ℝ))) :=
      mul_lt_mul_of_pos_left hprod (pow_pos (inv_pos.mpr hp0) _)
    _ = Real.log (p : ℝ) * (b + 1 : ℕ) := by
      rw [inv_pow]
      field_simp [hp0.ne']

/-- At the included endpoint, the price is at most q^b/b. This is the
price bound needed when copies below the cutoff exponent are missing. -/
private theorem cutoff_price_upper {z : ℝ} (hz : 4 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    Real.log (p : ℝ) / (z * Real.log z) ≤
      (p : ℝ)⁻¹ ^ cutoffExponent z p / (cutoffExponent z p : ℝ) := by
  let b := cutoffExponent z p
  obtain ⟨hb, hlo, _, _⟩ := cutoff_spec hz hp hpz
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : (b : ℝ) * Real.log (p : ℝ) ≤ Real.log z := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp0 b) hlo
  have hprod : (p : ℝ) ^ b * ((b : ℝ) * Real.log (p : ℝ)) ≤
      z * Real.log z :=
    mul_le_mul hlo hlog (by positivity) hz0.le
  apply (div_le_div_iff₀ (mul_pos hz0 hlz) hb0).mpr
  calc
    Real.log (p : ℝ) * (b : ℝ) =
        (p : ℝ)⁻¹ ^ b * ((p : ℝ) ^ b * ((b : ℝ) * Real.log (p : ℝ))) := by
      rw [inv_pow]
      field_simp [hp0.ne']
    _ ≤ (p : ℝ)⁻¹ ^ b * (z * Real.log z) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)

/-- The discrete compensation bracket; d=1 must be checked separately.
The d>=2 case uses p>=2 through q<=1/2. -/
private theorem bracket_nonneg {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 1 / 2)
    {b : ℕ} (hb : 1 ≤ b) (d : ℕ) :
    0 ≤ (b + 1 : ℕ) * q ^ d + (d : ℝ) - 1 / (1 - q) := by
  have hden : 0 < 1 - q := by linarith
  have hcap : 1 / (1 - q) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hB : (2 : ℝ) ≤ (b + 1 : ℕ) := by exact_mod_cast (show 2 ≤ b + 1 by omega)
  rcases d with _ | d
  · simp only [pow_zero, mul_one, Nat.cast_zero, add_zero]
    linarith
  · rcases d with _ | d
    · have hid : (b + 1 : ℕ) * q + 1 - 1 / (1 - q) =
          q * ((b + 1 : ℕ) - 1 / (1 - q)) := by
        field_simp [hden.ne']
        <;> ring
      simpa only [Nat.zero_add, pow_one, Nat.cast_one, hid] using
        mul_nonneg hq0.le (by linarith : 0 ≤ (b + 1 : ℕ) - 1 / (1 - q))
    · have hd : (2 : ℝ) ≤ (d + 1 + 1 : ℕ) := by exact_mod_cast (show 2 ≤ d + 1 + 1 by omega)
      have hpow : 0 ≤ (b + 1 : ℕ) * q ^ (d + 1 + 1) := by positivity
      linarith

/-- The p=2 bracket gives a uniform HALF-unit, including b=2,d=1. -/
private theorem two_bracket {b : ℕ} (hb : 2 ≤ b) (d : ℕ) :
    (1 / 2 : ℝ) ≤ (b + 1 : ℕ) * (1 / 2 : ℝ) ^ d + (d : ℝ) - 2 := by
  have hB : (3 : ℝ) ≤ (b + 1 : ℕ) := by exact_mod_cast (show 3 ≤ b + 1 by omega)
  rcases d with _ | _ | _ | d
  · norm_num only [pow_zero, mul_one, Nat.cast_zero, add_zero]
    linarith
  · norm_num only [pow_one, Nat.cast_one]
    linarith
  · norm_num only [Nat.cast_ofNat, pow_succ, pow_one]
    linarith
  · have hd : (3 : ℝ) ≤ (d + 1 + 1 + 1 : ℕ) := by exact_mod_cast (show 3 ≤ d + 1 + 1 + 1 by omega)
    have hpow : 0 ≤ (b + 1 : ℕ) * (1 / 2 : ℝ) ^ (d + 1 + 1 + 1) := by positivity
    linarith

/-- The logarithmic Euler tail strictly exceeds its first power term. -/
private theorem layer_tail_gt_first {n p : ℕ} (hp : p.Prime) :
    (p : ℝ)⁻¹ ^ (n.factorization p + 1) < layerTail n p := by
  have hq0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hq1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hpow0 : 0 < (p : ℝ)⁻¹ ^ (n.factorization p + 1) := pow_pos hq0 _
  have hpow1 : (p : ℝ)⁻¹ ^ (n.factorization p + 1) < 1 :=
    pow_lt_one₀ hq0.le hq1 (by omega)
  have hh := Real.log_lt_sub_one_of_pos (sub_pos.mpr hpow1)
    (by linarith : 1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1) ≠ 1)
  unfold layerTail
  linarith

private def primeContribution (z : ℝ) (n p : ℕ) : ℝ :=
  layerTail n p + ((n.factorization p : ℝ) - (cutoffExponent z p : ℝ)) *
    (Real.log (p : ℝ) / (z * Real.log z)) -
      shiftedTail (p : ℝ)⁻¹ (cutoffExponent z p)

/-- The local estimate is consumed by the actual finite prime sum below;
it assumes only a genuine exponent inventory, not correction positivity. -/
private theorem prime_contribution_lower {z : ℝ} (hz : 4 ≤ z) {n p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z)
    (ha : cutoffExponent z p ≤ n.factorization p) :
    let b := cutoffExponent z p
    let d := n.factorization p - b
    let q := (p : ℝ)⁻¹
    (q ^ (b + 1) / (b + 1 : ℕ)) *
      ((b + 1 : ℕ) * q ^ d + (d : ℝ) - 1 / (1 - q)) <
        primeContribution z n p := by
  let b := cutoffExponent z p
  let d := n.factorization p - b
  let q := (p : ℝ)⁻¹
  let A := q ^ (b + 1) / (b + 1 : ℕ)
  have hq0 : 0 < q := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hq1 : q < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hlog : q ^ (n.factorization p + 1) < layerTail n p :=
    layer_tail_gt_first hp
  have hsplit : q ^ (n.factorization p + 1) = q ^ (b + 1) * q ^ d := by
    have he : n.factorization p + 1 = (b + 1) + d := by dsimp [b, d] at *; omega
    rw [he, pow_add]
  have hprice : (d : ℝ) * A ≤
      (d : ℝ) * (Real.log (p : ℝ) / (z * Real.log z)) :=
    mul_le_mul_of_nonneg_left (cutoff_price hz hp hpz).le (Nat.cast_nonneg d)
  have htail : shiftedTail q b < A / (1 - q) := (shifted_tail_bound hq0 hq1 b).2
  have halgebra : A * ((b + 1 : ℕ) * q ^ d + (d : ℝ) - 1 / (1 - q)) =
      q ^ (b + 1) * q ^ d + (d : ℝ) * A - A / (1 - q) := by
    dsimp [A]
    field_simp [show ((b + 1 : ℕ) : ℝ) ≠ 0 by positivity,
      (sub_pos.mpr hq1).ne']
  rw [hsplit] at hlog
  calc
    A * ((b + 1 : ℕ) * q ^ d + (d : ℝ) - 1 / (1 - q)) =
        q ^ (b + 1) * q ^ d + (d : ℝ) * A - A / (1 - q) := halgebra
    _ < layerTail n p + (d : ℝ) *
        (Real.log (p : ℝ) / (z * Real.log z)) - shiftedTail q b := by linarith
    _ = primeContribution z n p := by
      have hd : (d : ℝ) = (n.factorization p : ℝ) - (b : ℝ) := by
        dsimp only [d]
        exact Nat.cast_sub ha
      dsimp only [primeContribution]
      rw [hd]

/-- Missing copies have a signed cost. Write b=a+1+e, so the shortfall
is e+1. The elementary e<2^e bound pays that shortfall from the first tail
term, while a whole geometric-series bound pays every reference layer. -/
private theorem prime_contribution_underfilled {z : ℝ} (hz : 4 ≤ z) {n p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z)
    (ha : 1 ≤ n.factorization p)
    (hab : n.factorization p < cutoffExponent z p) :
    (p : ℝ)⁻¹ ^ cutoffExponent z p / 6 < primeContribution z n p := by
  let a := n.factorization p
  let b := cutoffExponent z p
  let q := (p : ℝ)⁻¹
  let c := Real.log (p : ℝ) / (z * Real.log z)
  have hb2 : 2 ≤ b := by dsimp only [a, b] at *; omega
  obtain ⟨e, he⟩ : ∃ e : ℕ, b = a + 1 + e :=
    Nat.exists_eq_add_of_le (by dsimp only [a, b]; omega)
  have hq0 : 0 < q := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hq2 : q ≤ 1 / 2 := by
    simpa only [q, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p)
  have hq1 : q < 1 := by linarith
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hBR : (3 : ℝ) ≤ (b + 1 : ℕ) := by
    exact_mod_cast (show 3 ≤ b + 1 by omega)
  have hshort : e + 1 ≤ 2 ^ e := by
    have hh : e < 2 ^ e := Nat.lt_two_pow_self
    omega
  have hshortR : ((e + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ e := by
    exact_mod_cast hshort
  have hqpow : q ^ e ≤ (1 / 2 : ℝ) ^ e := pow_le_pow_left₀ hq0.le hq2 e
  have hunit : (2 : ℝ) ^ e * (1 / 2 : ℝ) ^ e = 1 := by
    rw [← mul_pow]
    norm_num
  have hshortq : ((e + 1 : ℕ) : ℝ) * q ^ e ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ e * (1 / 2 : ℝ) ^ e :=
        mul_le_mul hshortR hqpow (pow_nonneg hq0.le e) (by positivity)
      _ = 1 := hunit
  have hmass : ((e + 1 : ℕ) : ℝ) * q ^ b ≤ q ^ (a + 1) := by
    calc
      _ = q ^ (a + 1) * (((e + 1 : ℕ) : ℝ) * q ^ e) := by
        rw [he, pow_add]
        ring
      _ ≤ q ^ (a + 1) * 1 :=
        mul_le_mul_of_nonneg_left hshortq (pow_nonneg hq0.le _)
      _ = q ^ (a + 1) := mul_one _
  have hlog : q ^ (a + 1) < layerTail n p := layer_tail_gt_first hp
  have hprice : c ≤ q ^ b / (b : ℝ) := cutoff_price_upper hz hp hpz
  have hdebt : ((e + 1 : ℕ) : ℝ) * c ≤
      ((e + 1 : ℕ) : ℝ) * (q ^ b / (b : ℝ)) :=
    mul_le_mul_of_nonneg_left hprice (Nat.cast_nonneg _)
  have hcap : q / (1 - q) ≤ 1 :=
    (div_le_one (sub_pos.mpr hq1)).mpr (by linarith)
  have hreference : (q ^ (b + 1) / (b + 1 : ℕ)) / (1 - q) ≤
      q ^ b / (b + 1 : ℕ) := by
    calc
      _ = (q ^ b / (b + 1 : ℕ)) * (q / (1 - q)) := by
        rw [pow_succ]
        ring
      _ ≤ (q ^ b / (b + 1 : ℕ)) * 1 :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = q ^ b / (b + 1 : ℕ) := mul_one _
  have htail : shiftedTail q b < q ^ b / (b + 1 : ℕ) :=
    (shifted_tail_bound hq0 hq1 b).2.trans_le hreference
  have hsigned : (a : ℝ) - (b : ℝ) = -((e + 1 : ℕ) : ℝ) := by
    rw [he]
    push_cast
    ring
  have halgebra : q ^ b * (((e + 1 : ℕ) : ℝ) * (1 - 1 / (b : ℝ)) -
        1 / (b + 1 : ℕ)) =
      ((e + 1 : ℕ) : ℝ) * q ^ b -
        ((e + 1 : ℕ) : ℝ) * (q ^ b / (b : ℝ)) - q ^ b / (b + 1 : ℕ) := by
    ring
  have hraw : q ^ b * (((e + 1 : ℕ) : ℝ) * (1 - 1 / (b : ℝ)) -
        1 / (b + 1 : ℕ)) < primeContribution z n p := by
    change _ < layerTail n p + ((a : ℝ) - (b : ℝ)) * c - shiftedTail q b
    rw [hsigned, halgebra]
    linarith only [hmass, hlog, hdebt, htail]
  have hib : 1 / (b : ℝ) ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hbR
  have hiB : 1 / (b + 1 : ℕ) ≤ (1 / 3 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hBR
  have hshort1 : (1 : ℝ) ≤ (e + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ e + 1 by omega)
  have hmul := mul_le_mul_of_nonneg_right hshort1
    (by linarith : 0 ≤ 1 - 1 / (b : ℝ))
  have hbracket : (1 / 6 : ℝ) ≤
      ((e + 1 : ℕ) : ℝ) * (1 - 1 / (b : ℝ)) - 1 / (b + 1 : ℕ) := by
    linarith only [hib, hiB, hmul]
  calc
    q ^ b / 6 = q ^ b * (1 / 6 : ℝ) := by ring
    _ ≤ q ^ b * (((e + 1 : ℕ) : ℝ) * (1 - 1 / (b : ℝ)) -
        1 / (b + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hbracket (pow_nonneg hq0.le _)
    _ < primeContribution z n p := hraw

/-- The p=2 half-unit is at least the advertised original z-scale bound. -/
private theorem two_scale {z : ℝ} (hz : 4 ≤ z) :
    Real.log 2 / (6 * z * Real.log z) ≤
      (((2 : ℝ)⁻¹ ^ (cutoffExponent z 2 + 1)) /
        (cutoffExponent z 2 + 1 : ℕ)) * (1 / 2) := by
  let b := cutoffExponent z 2
  obtain ⟨_, hlo, _, hbn⟩ := cutoff_spec hz Nat.prime_two (by norm_num; linarith)
  have hb : 2 ≤ b := by
    rw [show b = Nat.log 2 ⌊z⌋₊ from hbn]
    exact Nat.le_log_of_pow_le (by norm_num) (Nat.le_floor hz)
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (b : ℝ) * Real.log 2 ≤ Real.log z := by
    simpa only [Real.log_pow] using Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ b) hlo
  have hprod : (2 : ℝ) ^ b * ((b : ℝ) * Real.log 2) ≤ z * Real.log z :=
    mul_le_mul hlo hlog (by positivity) hz0.le
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hsmall : (4 : ℝ) * (b + 1 : ℕ) ≤ (6 : ℝ) * b := by push_cast; linarith
  have hcross : Real.log 2 * (2 * (b + 1 : ℕ) * (2 : ℝ) ^ (b + 1)) ≤
      (6 * z * Real.log z : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) b) hl2.le)
    rw [pow_succ]
    nlinarith
  have hh : Real.log 2 / (6 * z * Real.log z) ≤
      1 / (2 * (b + 1 : ℕ) * (2 : ℝ) ^ (b + 1)) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * z * Real.log z)
      (by positivity : (0 : ℝ) < 2 * (b + 1 : ℕ) * (2 : ℝ) ^ (b + 1))).mpr
    simpa only [one_mul] using hcross
  calc
    _ ≤ 1 / (2 * (b + 1 : ℕ) * (2 : ℝ) ^ (b + 1)) := hh
    _ = (((2 : ℝ)⁻¹ ^ (b + 1)) / (b + 1 : ℕ)) * (1 / 2) := by
      rw [inv_pow]
      field_simp
      <;> ring

private theorem full_surplus_eq_sum {z : ℝ} (hz : 4 ≤ z) {n : ℕ}
    (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
      fullPrimePowerResidual z =
        ∑ p ∈ Nat.primesLE ⌊z⌋₊, primeContribution z n p := by
  classical
  let S := Nat.primesLE ⌊z⌋₊
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hle (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≤ z :=
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).1 : (p : ℝ) ≤ ⌊z⌋₊).trans
      (Nat.floor_le (by linarith : 0 ≤ z))
  have hmass : Real.log (n : ℝ) - Chebyshev.psi z =
      ∑ p ∈ S, ((n.factorization p : ℝ) - (cutoffExponent z p : ℝ)) *
        Real.log (p : ℝ) := by
    have hlog : Real.log (n : ℝ) =
        ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
      rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, hsupport]
    have hpsi : Chebyshev.psi z =
        ∑ p ∈ S, (cutoffExponent z p : ℝ) * Real.log (p : ℝ) := by
      rw [Chebyshev.psi_eq_psi_coe_floor z, Chebyshev.psi_eq_sum_mul_log_prime]
      apply sum_congr rfl
      intro p hp
      rw [(cutoff_spec hz (hprime p hp) (hle p hp)).2.2.2]
    rw [hlog, hpsi, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  have hres : fullPrimePowerResidual z =
      ∑ p ∈ S, shiftedTail (p : ℝ)⁻¹ (cutoffExponent z p) := by
    unfold fullPrimePowerResidual
    apply sum_congr rfl
    intro p hp
    exact residual_prime_eq_shift hz (hprime p hp) (hle p hp)
  change tail n + (Real.log (n : ℝ) - Chebyshev.psi z) /
      (z * Real.log z) - fullPrimePowerResidual z = ∑ p ∈ S, primeContribution z n p
  rw [tail, hsupport, hmass, hres, sum_div, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  dsimp [primeContribution]
  ring

private theorem prime_contribution_pos {z : ℝ} (hz : 4 ≤ z) {n p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) (ha : 1 ≤ n.factorization p) :
    0 < primeContribution z n p := by
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  by_cases hab : cutoffExponent z p ≤ n.factorization p
  · have hi2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p)
    have hbr := bracket_nonneg hi0 hi2 (cutoff_spec hz hp hpz).1
      (n.factorization p - cutoffExponent z p)
    exact lt_of_le_of_lt (mul_nonneg (by positivity) hbr)
      (prime_contribution_lower hz hp hpz hab)
  · exact (div_pos (pow_pos hi0 _) (by norm_num : (0 : ℝ) < 6)).trans
      (prime_contribution_underfilled hz hp hpz ha (lt_of_not_ge hab))

/-- Full arithmetic surplus for every positive integer on the exact
initial prime support. The valuation inventory is signed, with no premise
requiring the integer to contain the prime powers at most z. -/
theorem full_prime_power_arithmetic_surplus {z : ℝ} (hz : 4 ≤ z) {n : ℕ}
    (hn : 0 < n)
    (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    Real.log 2 / (6 * z * Real.log z) <
      tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
        fullPrimePowerResidual z := by
  classical
  let S := Nat.primesLE ⌊z⌋₊
  have hz0 : 0 ≤ z := by linarith
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hle (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≤ z :=
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).1 : (p : ℝ) ≤ ⌊z⌋₊).trans
      (Nat.floor_le hz0)
  have hval (p : ℕ) (hp : p ∈ S) : 1 ≤ n.factorization p := by
    have hpSupport : p ∈ n.primeFactors := by rw [hsupport]; exact hp
    exact (hprime p hp).factorization_pos_of_dvd hn.ne'
      (Nat.dvd_of_mem_primeFactors hpSupport)
  have hidentity := full_surplus_eq_sum hz hsupport
  have hpositive (p : ℕ) (hp : p ∈ S) : 0 < primeContribution z n p :=
    prime_contribution_pos hz (hprime p hp) (hle p hp) (hval p hp)
  have h2 : 2 ∈ S := Nat.mem_primesLE.mpr ⟨Nat.le_floor (by linarith : (2 : ℝ) ≤ z), Nat.prime_two⟩
  have hb2 : 2 ≤ cutoffExponent z 2 := by
    rw [(cutoff_spec hz Nat.prime_two (hle 2 h2)).2.2.2]
    exact Nat.le_log_of_pow_le (by norm_num) (Nat.le_floor hz)
  have htwo : (((2 : ℝ)⁻¹ ^ (cutoffExponent z 2 + 1)) /
        (cutoffExponent z 2 + 1 : ℕ)) * (1 / 2) < primeContribution z n 2 := by
    by_cases ha : cutoffExponent z 2 ≤ n.factorization 2
    · have hbr2 := two_bracket hb2 (n.factorization 2 - cutoffExponent z 2)
      apply lt_of_le_of_lt _ (prime_contribution_lower hz Nat.prime_two (hle 2 h2) ha)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hbr2 using 1 <;> norm_num
    · have hlow := prime_contribution_underfilled hz Nat.prime_two (hle 2 h2)
        (hval 2 h2) (lt_of_not_ge ha)
      have hB : (3 : ℝ) ≤ (cutoffExponent z 2 + 1 : ℕ) := by
        exact_mod_cast (show 3 ≤ cutoffExponent z 2 + 1 by omega)
      have hB0 : (0 : ℝ) < (cutoffExponent z 2 + 1 : ℕ) := by linarith
      have hpay : (((2 : ℝ)⁻¹ ^ (cutoffExponent z 2 + 1)) /
            (cutoffExponent z 2 + 1 : ℕ)) * (1 / 2) ≤
          (2 : ℝ)⁻¹ ^ cutoffExponent z 2 / 6 := by
        calc
          _ = (2 : ℝ)⁻¹ ^ cutoffExponent z 2 /
              (4 * (cutoffExponent z 2 + 1 : ℕ)) := by
            rw [pow_succ]
            norm_num <;> field_simp [hB0.ne'] <;> ring
          _ ≤ (2 : ℝ)⁻¹ ^ cutoffExponent z 2 / 6 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      exact hpay.trans_lt hlow
  rw [hidentity]
  exact (two_scale hz).trans_lt (htwo.trans_le
    (single_le_sum (fun p hp => (hpositive p hp).le) h2))

/-- An explicit finite-domain consequence of Mathlib's elementary Chebyshev bound. -/
private theorem theta_quarter {x : ℝ} (hx : 4096 ≤ x) : x / 4 < Chebyshev.theta x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 64 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < Real.sqrt x := by linarith
  have hsq := Real.sq_sqrt hx0
  have h2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have h2lo : (2 / 3 : ℝ) < Real.log 2 := by
    have hh := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at hh ⊢
    exact hh
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hu := Real.log_le_sub_one_of_pos (div_pos hs0 (by norm_num : (0 : ℝ) < 64))
  rw [Real.log_div hs0.ne' (by norm_num), Real.log_sqrt hx0, h64] at hu
  have hlog : Real.log x ≤ (3 / 16 : ℝ) * Real.sqrt x := by linarith
  have hsx : 64 * Real.sqrt x ≤ x := by nlinarith
  have hlogplus : Real.log (x + 2) ≤ 1 + 3 * x / 1024 := by
    have hm := Real.log_le_log (by linarith : 0 < x + 2)
      (by linarith : x + 2 ≤ 2 * x)
    rw [Real.log_mul (by norm_num) (by linarith : x ≠ 0)] at hm
    linarith
  have hprod : 2 * Real.sqrt x * Real.log x ≤ 3 * x / 8 := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * Real.sqrt x)
    nlinarith only [hh, hsq]
  have hlo := Chebyshev.theta_ge' (by linarith : 1 ≤ x)
  have hh := mul_le_mul_of_nonneg_left h2lo.le (by linarith : 0 ≤ x - 1)
  nlinarith only [hx, hlo, hh, hlogplus, hprod]

/-- In the actual band, the price of a second copy is essential: the
estimate holds for every positive actual valuation, including a>=2. -/
private theorem prime_contribution_gt_third_inv_sq {z : ℝ} (hz : 4 ≤ z) {n p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z)
    (hroot : 2 * Real.sqrt z < (p : ℝ)) (ha : 1 ≤ n.factorization p) :
    (p : ℝ)⁻¹ ^ 2 / 3 < primeContribution z n p := by
  let q : ℝ := (p : ℝ)⁻¹
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hs0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
  have hs2 : 2 ≤ Real.sqrt z := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq := Real.sq_sqrt hz0.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp4 : (4 : ℝ) < p := by linarith
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq4 : q < 1 / 4 := by
    dsimp [q]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hp4
  have hq1 : q < 1 := by linarith
  have hpsq : 4 * z < (p : ℝ) ^ 2 := by nlinarith
  have hb : cutoffExponent z p = 1 := by
    have hb1 := (cutoff_spec hz hp hpz).1
    have hb2 := (cutoff_lt_iff hz hp hpz 2).mpr (by linarith)
    omega
  have htail : shiftedTail q 1 < (2 / 3 : ℝ) * q ^ 2 := by
    have ht := (shifted_tail_bound hq0 hq1 1).2
    norm_num at ht
    have hden : 0 < 1 - q := by linarith
    have hbound : q ^ 2 / 2 / (1 - q) ≤ (2 / 3 : ℝ) * q ^ 2 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [sq_nonneg q]
    exact ht.trans_le hbound
  have hqq : q ^ 2 * (p : ℝ) ^ 2 = 1 := by
    dsimp [q]
    rw [← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow]
  have hqz : 4 * z * q ^ 2 < 1 := by
    have hh := mul_lt_mul_of_pos_right hpsq (sq_pos_of_pos hq0)
    nlinarith only [hh, hqq]
  have hlogp : Real.log z / 2 < Real.log (p : ℝ) := by
    rw [← Real.log_sqrt hz0.le]
    exact Real.log_lt_log (by linarith) (by linarith)
  have hprice : 2 * q ^ 2 < Real.log (p : ℝ) / (z * Real.log z) := by
    apply (lt_div_iff₀ (mul_pos hz0 hlz)).mpr
    have hm := mul_lt_mul_of_pos_right hqz hlz
    nlinarith only [hm, hlogp]
  have hlayer : 0 < layerTail n p :=
    (pow_pos hq0 _).trans (layer_tail_gt_first hp)
  change q ^ 2 / 3 < _
  unfold primeContribution
  rw [hb]
  norm_num only [Nat.cast_one]
  by_cases ha1 : n.factorization p = 1
  · have hf := layer_tail_gt_first (n := n) hp
    rw [ha1] at hf ⊢
    norm_num at hf ⊢
    dsimp [q] at htail ⊢
    simp only [inv_pow] at htail ⊢
    linarith
  · have ha2 : (2 : ℝ) ≤ n.factorization p := by
      exact_mod_cast (show 2 ≤ n.factorization p by omega)
    have hprice0 : 0 ≤ Real.log (p : ℝ) / (z * Real.log z) := by positivity
    have hh := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ (n.factorization p : ℝ) - 1) hprice0
    dsimp [q] at htail hprice ⊢
    nlinarith only [hh, hlayer, htail, hprice, sq_nonneg ((p : ℝ)⁻¹)]

/-- Explicit root-scale surplus on the entire finite domain z>=4. The
signed valuation inventory and the complete infinite residual are unchanged. -/
theorem full_prime_power_arithmetic_surplus_root_scale {z : ℝ} (hz : 4 ≤ z) {n : ℕ}
    (hn : 0 < n) (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    1 / (2000 * Real.sqrt z * Real.log z) <
      tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
        fullPrimePowerResidual z := by
  classical
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hy0 : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz0
  have hsq := Real.sq_sqrt hz0.le
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    have hh := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at hh ⊢
    exact hh
  by_cases hsmall : z ≤ 16384
  · have hy : Real.sqrt z ≤ 128 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
    apply lt_trans _ (full_prime_power_arithmetic_surplus hz hn hsupport)
    apply (div_lt_div_iff₀ (by positivity : 0 < 2000 * Real.sqrt z * Real.log z)
      (by positivity : 0 < 6 * z * Real.log z)).mpr
    have hyy : z ≤ 128 * Real.sqrt z := by nlinarith
    have hlogmul := mul_lt_mul_of_pos_right hlog2 (by positivity : 0 < 2000 * Real.sqrt z)
    have hfinal : 6 * z < Real.log 2 * (2000 * Real.sqrt z) := by nlinarith
    nlinarith only [mul_lt_mul_of_pos_right hfinal hlz]
  have hlarge : 16384 ≤ z := le_of_lt (lt_of_not_ge hsmall)
  have hy : 128 ≤ Real.sqrt z := Real.le_sqrt_of_sq_le (by nlinarith)
  have htop : 32 * Real.sqrt z ≤ z := by nlinarith
  let S := Nat.primesLE ⌊z⌋₊
  let T := Nat.primesLE ⌊32 * Real.sqrt z⌋₊
  let U := Nat.primesLE ⌊2 * Real.sqrt z⌋₊
  let B := T \ U
  have hUT : U ⊆ T := Nat.primesLE_mono (Nat.floor_mono (by nlinarith))
  have hTS : T ⊆ S := Nat.primesLE_mono (Nat.floor_mono htop)
  have hBS : B ⊆ S := fun p hp => hTS (mem_sdiff.mp hp).1
  have hB (p : ℕ) (hp : p ∈ B) : p.Prime ∧
      2 * Real.sqrt z < (p : ℝ) ∧ (p : ℝ) ≤ 32 * Real.sqrt z := by
    obtain ⟨hpT, hpU⟩ := mem_sdiff.mp hp
    obtain ⟨hpTop, hpp⟩ := Nat.mem_primesLE.mp hpT
    have hpTopR : (p : ℝ) ≤ 32 * Real.sqrt z :=
      (Nat.le_floor_iff (by positivity)).mp hpTop
    refine ⟨hpp, ?_, hpTopR⟩
    by_contra h
    apply hpU
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (le_of_not_gt h), hpp⟩
  have hsum : ∑ p ∈ B, Real.log (p : ℝ) =
      Chebyshev.theta (32 * Real.sqrt z) - Chebyshev.theta (2 * Real.sqrt z) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    exact sum_sdiff_eq_sub hUT
  have hquarter := theta_quarter (by nlinarith : 4096 ≤ 32 * Real.sqrt z)
  have hupper := Chebyshev.theta_le_log4_mul_x (by positivity : 0 ≤ 2 * Real.sqrt z)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hmass0 : 4 * Real.sqrt z < ∑ p ∈ B, Real.log (p : ℝ) := by
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_right hlog4 (by positivity : 0 ≤ 2 * Real.sqrt z)
    nlinarith only [hquarter, hupper, hh]
  have hmass : 4 * Real.sqrt z < (B.card : ℝ) * Real.log z := by
    apply hmass0.trans_le
    calc
      _ ≤ ∑ _p ∈ B, Real.log z := sum_le_sum fun p hp =>
        Real.log_le_log (by exact_mod_cast (hB p hp).1.pos)
          ((hB p hp).2.2.trans htop)
      _ = _ := by simp
  have hpos (p : ℕ) (hp : p ∈ S) : 0 < primeContribution z n p := by
    obtain ⟨hpf, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpz : (p : ℝ) ≤ z := (Nat.le_floor_iff hz0.le).mp hpf
    have hpn : p ∈ n.primeFactors := by rw [hsupport]; exact hp
    exact prime_contribution_pos hz hpp hpz
      (hpp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hpn))
  have hlocal (p : ℕ) (hp : p ∈ B) :
      1 / (3072 * z) ≤ primeContribution z n p := by
    obtain ⟨hpp, hroot, hpTop⟩ := hB p hp
    have hpz : (p : ℝ) ≤ z := hpTop.trans htop
    have hpn : p ∈ n.primeFactors := by rw [hsupport]; exact hBS hp
    have ha := hpp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hpn)
    have hc := prime_contribution_gt_third_inv_sq hz hpp hpz hroot ha
    apply le_trans _ hc.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpsq : (p : ℝ) ^ 2 ≤ 1024 * z := by nlinarith
    have heq : (p : ℝ)⁻¹ ^ 2 / 3 = 1 / (3 * (p : ℝ) ^ 2) := by
      field_simp
    rw [heq]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hbound : (B.card : ℝ) / (3072 * z) ≤
      tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
        fullPrimePowerResidual z := by
    rw [full_surplus_eq_sum hz hsupport]
    calc
      _ = ∑ _p ∈ B, 1 / (3072 * z) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ B, primeContribution z n p := sum_le_sum hlocal
      _ ≤ ∑ p ∈ S, primeContribution z n p :=
        sum_le_sum_of_subset_of_nonneg hBS (fun p hp _ => (hpos p hp).le)
  apply lt_of_lt_of_le _ hbound
  apply (div_lt_div_iff₀ (by positivity : 0 < 2000 * Real.sqrt z * Real.log z)
    (by positivity : 0 < 3072 * z)).mpr
  have hm := mul_lt_mul_of_pos_right hmass (by positivity : 0 < 768 * Real.sqrt z)
  have hcard : 0 ≤ (B.card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hcard (mul_pos hy0 hlz).le]

/-- Exact finite Mangoldt reindexing. The root cutoff is retained as a
filter, so extending to the common prime support inserts only zero terms. -/
private theorem mangoldt_prefix_eq {z : ℝ} (hz : 4 ≤ z) :
    (∑ d ∈ Ioc 0 ⌊z⌋₊,
      ArithmeticFunction.vonMangoldt d / ((d : ℝ) * Real.log d)) =
    ∑ p ∈ Nat.primesLE ⌊z⌋₊, ∑ k ∈ Icc 1 (cutoffExponent z p),
      (p : ℝ)⁻¹ ^ k / (k : ℝ) := by
  classical
  let K := ⌊Real.log z / Real.log 2⌋₊
  let S := Nat.primesLE ⌊z⌋₊
  have hz0 : 0 ≤ z := by linarith
  have hroot (k : ℕ) (hk : k ∈ Icc 1 K) :
      (Ioc 0 ⌊z ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime =
        S.filter (fun p => k ≤ cutoffExponent z p) := by
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    ext p
    constructor
    · intro hp
      obtain ⟨hpm, hpp⟩ := mem_filter.mp hp
      have hpr : (p : ℝ) ≤ z ^ (1 / (k : ℝ)) :=
        (Nat.le_floor_iff (Real.rpow_nonneg hz0 _)).mp (mem_Ioc.mp hpm).2
      have hpow : (p : ℝ) ^ k ≤ z := by
        rw [one_div] at hpr
        have hh := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) hz0 hk0).mp hpr
        simpa only [Real.rpow_natCast] using hh
      have hpz : (p : ℝ) ≤ z :=
        (le_self_pow₀ (by exact_mod_cast hpp.one_le) (by omega : k ≠ 0)).trans hpow
      apply mem_filter.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpz, hpp⟩, ?_⟩
      by_contra h
      exact (not_lt_of_ge hpow) ((cutoff_lt_iff hz hpp hpz k).mp (lt_of_not_ge h))
    · intro hp
      obtain ⟨hpS, hkb⟩ := mem_filter.mp hp
      obtain ⟨hpf, hpp⟩ := Nat.mem_primesLE.mp hpS
      have hpz : (p : ℝ) ≤ z := (Nat.le_floor_iff hz0).mp hpf
      have hpow : (p : ℝ) ^ k ≤ z :=
        (pow_le_pow_right₀ (by exact_mod_cast hpp.one_le) hkb).trans
          (cutoff_spec hz hpp hpz).2.1
      have hpr : (p : ℝ) ≤ z ^ (1 / (k : ℝ)) := by
        rw [one_div]
        apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) hz0 hk0).mpr
        simpa only [Real.rpow_natCast] using hpow
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, Nat.le_floor hpr⟩, hpp⟩
  have hbK (p : ℕ) (hp : p ∈ S) : cutoffExponent z p ≤ K := by
    obtain ⟨hpf, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpz : (p : ℝ) ≤ z := (Nat.le_floor_iff hz0).mp hpf
    change cutoffExponent z p ≤ cutoffExponent z 2
    rw [(cutoff_spec hz hpp hpz).2.2.2,
      (cutoff_spec hz Nat.prime_two (by linarith : (2 : ℝ) ≤ z)).2.2.2]
    exact Nat.log_anti_left (by norm_num) hpp.two_le
  simp_rw [ArithmeticFunction.vonMangoldt_apply, ite_div, zero_div, ← sum_filter]
  rw [Chebyshev.sum_PrimePow_eq_sum_sum _ hz0]
  calc
    _ = ∑ k ∈ Icc 1 K,
        ∑ p ∈ (Ioc 0 ⌊z ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
          (p : ℝ)⁻¹ ^ k / (k : ℝ) := by
      refine sum_congr rfl fun k hk => sum_congr rfl fun p hp => ?_
      have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
      have hpp := (mem_filter.mp hp).2
      have hkp : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      have hlp : Real.log (p : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
      rw [Nat.Prime.pow_minFac hpp hk0]
      simp only [Nat.cast_pow, Real.log_pow, inv_pow]
      field_simp [hlp, hkp, hp0]
    _ = ∑ k ∈ Icc 1 K, ∑ p ∈ S.filter (fun p => k ≤ cutoffExponent z p),
        (p : ℝ)⁻¹ ^ k / (k : ℝ) := by
      apply sum_congr rfl
      intro k hk
      rw [hroot k hk]
    _ = ∑ p ∈ S, ∑ k ∈ Icc 1 (cutoffExponent z p),
        (p : ℝ)⁻¹ ^ k / (k : ℝ) := by
      simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [← sum_filter]
      congr 1
      ext k
      simp only [mem_filter, mem_Icc]
      have := hbK p hp
      omega

/-- A genuinely summable complete Euler logarithm is split at b. Its
remaining shifted series is exactly the original strict prime-power residual. -/
private theorem prime_prefix_add_residual {z : ℝ} (hz : 4 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    (∑ k ∈ Icc 1 (cutoffExponent z p), (p : ℝ)⁻¹ ^ k / (k : ℝ)) +
      (∑' k : ℕ, if 2 ≤ k ∧ z < (p : ℝ) ^ k then
        (p : ℝ)⁻¹ ^ k / (k : ℝ) else 0) =
      -Real.log (1 - 1 / (p : ℝ)) := by
  let b := cutoffExponent z p
  let G : ℕ → ℝ := fun r => (p : ℝ)⁻¹ ^ (r + 1) / (r + 1 : ℕ)
  have hG : HasSum G (-Real.log (1 - 1 / (p : ℝ))) := by
    convert (Mertens.HasSum_log_one_sub_one_div_prime hp).neg using 1
    ext r
    dsimp [G]
    simp only [Pi.neg_apply, neg_div, neg_neg, Nat.cast_add, Nat.cast_one, inv_pow]
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
    <;> ring
  have hsplit := hG.summable.sum_add_tsum_nat_add b
  rw [hG.tsum_eq] at hsplit
  have hprefix : (∑ k ∈ Icc 1 b, (p : ℝ)⁻¹ ^ k / (k : ℝ)) =
      ∑ r ∈ range b, G r := by
    rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    apply sum_congr rfl
    intro r hr
    simp only [G, Nat.add_comm]
  rw [residual_prime_eq_shift hz hp hpz, hprefix]
  change (∑ r ∈ range b, G r) + shiftedTail (p : ℝ)⁻¹ b = _
  simpa only [shiftedTail, G, Nat.add_assoc] using hsplit

/-- Exact complete arithmetic ledger: no prime power or convergent Euler
series tail is dropped. Equality at p^k=z belongs to the finite prefix. -/
theorem complete_mangoldt_add_E3_eq_neg_residual {z : ℝ} (hz : 4 ≤ z) :
    Mertens.E₂Λ z + Mertens.E₃ z = -fullPrimePowerResidual z := by
  classical
  have hsum : (∑ d ∈ Ioc 0 ⌊z⌋₊,
      ArithmeticFunction.vonMangoldt d / ((d : ℝ) * Real.log d)) +
      fullPrimePowerResidual z =
      ∑ p ∈ Nat.primesLE ⌊z⌋₊, -Real.log (1 - 1 / (p : ℝ)) := by
    rw [mangoldt_prefix_eq hz, fullPrimePowerResidual, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hpf, hpp⟩ := Nat.mem_primesLE.mp hp
    exact prime_prefix_add_residual hz hpp ((Nat.le_floor_iff (by linarith)).mp hpf)
  rw [Mertens.E₂Λ, Mertens.E₃, Mertens.γ.eq_eulerMascheroni]
  rw [Nat.primesLE_eq_filter_Ioc_zero, sum_neg_distrib] at hsum
  linarith only [hsum]

end D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
