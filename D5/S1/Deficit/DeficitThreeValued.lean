/- GID: D5/S1/Deficit/DeficitThreeValued
   generality: I
   mirror-B: D5/B/S1/Deficit/DeficitThreeValued
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   digest: The normalized beta deficit of golden addition takes only the values -1, 0, and 1. -/

import D5.S1.Deficit.DeficitInteger
import Mathlib.Analysis.SpecificLimits.Basic

/- Provenance: contraction-face window bound over pinned mathlib geometric series
   (`summable_geometric_of_lt_one`, `tsum_geometric_of_lt_one`,
   `Function.Injective.tsum_eq`, `Summable.sum_le_tsum`) intersected with the
   integer certificate exported by `deficit_integer`. -/

namespace D5.S1.Deficit

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Digit
open D5.S1.Scale
open Real

/-! ### Elementary golden-conjugate facts

The contraction face evaluates Zeckendorf digits at powers of the golden
conjugate `psi = (1 - sqrt 5) / 2`, which satisfies `-1 < psi < 0` and
`psi ^ 2 = psi + 1`.  The window endpoints are `-psi ^ 2 = -1 / phi ^ 2` and
`-psi = 1 / phi`, and the window has length exactly one. -/

private theorem goldenConj_nonpos : goldenConj ≤ 0 := goldenConj_neg.le

private theorem neg_goldenConj_nonneg : (0 : ℝ) ≤ -goldenConj := by
  have := goldenConj_neg; linarith

private theorem neg_goldenConj_lt_one : -goldenConj < 1 := by
  have := neg_one_lt_goldenConj; linarith

private theorem neg_goldenConj_ne_zero : -goldenConj ≠ 0 :=
  neg_ne_zero.mpr goldenConj_ne_zero

private theorem goldenConj_sq_nonneg : (0 : ℝ) ≤ goldenConj ^ 2 := sq_nonneg _

private theorem goldenConj_sq_lt_one : goldenConj ^ 2 < 1 := by
  rw [goldenConj_sq]; have := goldenConj_neg; linarith

private theorem one_sub_goldenConj_sq : 1 - goldenConj ^ 2 = -goldenConj := by
  rw [goldenConj_sq]; ring

/-! ### The even and odd parts of the contraction-face series

Splitting the psi-power series over even and odd exponents isolates the
positive and negative contributions.  Each part is dominated by a geometric
series with ratio `psi ^ 2`, and the two full sums are the window endpoints. -/

private noncomputable def evenPart (i : ℕ) : ℝ :=
  if Even i then goldenConj ^ (i + 2) else 0

private noncomputable def oddPart (i : ℕ) : ℝ :=
  if Odd i then -(goldenConj ^ (i + 2)) else 0

private theorem evenPart_nonneg (i : ℕ) : 0 ≤ evenPart i := by
  rw [evenPart]
  split
  · rename_i h
    exact (h.add even_two).pow_nonneg goldenConj
  · exact le_refl 0

private theorem oddPart_nonneg (i : ℕ) : 0 ≤ oddPart i := by
  rw [oddPart]
  split
  · rename_i h
    have := (h.add_even even_two).pow_nonpos goldenConj_nonpos
    linarith
  · exact le_refl 0

private theorem evenPart_le_geometric (i : ℕ) :
    evenPart i ≤ goldenConj ^ 2 * (-goldenConj) ^ i := by
  have hterm : 0 ≤ goldenConj ^ 2 * (-goldenConj) ^ i :=
    mul_nonneg goldenConj_sq_nonneg (pow_nonneg neg_goldenConj_nonneg i)
  rw [evenPart]
  split
  · rename_i h
    have hneg : (-goldenConj) ^ i = goldenConj ^ i := h.neg_pow goldenConj
    have hsplit : goldenConj ^ (i + 2) = goldenConj ^ i * goldenConj ^ 2 := pow_add _ _ _
    rw [hneg, hsplit]
    exact le_of_eq (mul_comm _ _)
  · exact hterm

private theorem oddPart_le_geometric (i : ℕ) :
    oddPart i ≤ goldenConj ^ 2 * (-goldenConj) ^ i := by
  have hterm : 0 ≤ goldenConj ^ 2 * (-goldenConj) ^ i :=
    mul_nonneg goldenConj_sq_nonneg (pow_nonneg neg_goldenConj_nonneg i)
  rw [oddPart]
  split
  · rename_i h
    have hneg : (-goldenConj) ^ i = -goldenConj ^ i := h.neg_pow goldenConj
    have hsplit : goldenConj ^ (i + 2) = goldenConj ^ i * goldenConj ^ 2 := pow_add _ _ _
    rw [hsplit, hneg]
    exact le_of_eq (by ring)
  · exact hterm

private theorem geometric_summable :
    Summable fun i : ℕ => goldenConj ^ 2 * (-goldenConj) ^ i :=
  (summable_geometric_of_lt_one neg_goldenConj_nonneg neg_goldenConj_lt_one).mul_left _

private theorem evenPart_summable : Summable evenPart :=
  Summable.of_nonneg_of_le evenPart_nonneg evenPart_le_geometric geometric_summable

private theorem oddPart_summable : Summable oddPart :=
  Summable.of_nonneg_of_le oddPart_nonneg oddPart_le_geometric geometric_summable

private theorem sq_geometric_tsum :
    ∑' j : ℕ, (goldenConj ^ 2) ^ j = (-goldenConj)⁻¹ := by
  rw [tsum_geometric_of_lt_one goldenConj_sq_nonneg goldenConj_sq_lt_one,
    one_sub_goldenConj_sq]

private theorem evenPart_tsum : ∑' i : ℕ, evenPart i = -goldenConj := by
  have hinj : Function.Injective fun j : ℕ => 2 * j := fun a b h => by
    dsimp only at h; omega
  have hsupp : Function.support evenPart ⊆ Set.range fun j : ℕ => 2 * j := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_cases hev : Even x
    · obtain ⟨r, hr⟩ := hev
      exact ⟨r, by change 2 * r = x; omega⟩
    · exact absurd (by rw [evenPart, if_neg hev]) hx
  have hval : ∀ j : ℕ, evenPart (2 * j) = goldenConj ^ 2 * (goldenConj ^ 2) ^ j := by
    intro j
    have hev : Even (2 * j) := ⟨j, by omega⟩
    have hexp : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [evenPart, if_pos hev, hexp, pow_mul, pow_succ]
    ring
  calc ∑' i : ℕ, evenPart i
      = ∑' j : ℕ, evenPart (2 * j) := (hinj.tsum_eq hsupp).symm
    _ = ∑' j : ℕ, goldenConj ^ 2 * (goldenConj ^ 2) ^ j := tsum_congr hval
    _ = goldenConj ^ 2 * (-goldenConj)⁻¹ := by rw [tsum_mul_left, sq_geometric_tsum]
    _ = -goldenConj := by
        have hsq : goldenConj ^ 2 = -goldenConj * -goldenConj := by ring
        rw [hsq, mul_inv_cancel_right₀ neg_goldenConj_ne_zero]

private theorem oddPart_tsum : ∑' i : ℕ, oddPart i = goldenConj ^ 2 := by
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := fun a b h => by
    dsimp only at h; omega
  have hsupp : Function.support oddPart ⊆ Set.range fun j : ℕ => 2 * j + 1 := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_cases hodd : Odd x
    · obtain ⟨r, hr⟩ := hodd
      exact ⟨r, by change 2 * r + 1 = x; omega⟩
    · exact absurd (by rw [oddPart, if_neg hodd]) hx
  have hval : ∀ j : ℕ,
      oddPart (2 * j + 1) = (-goldenConj) ^ 3 * (goldenConj ^ 2) ^ j := by
    intro j
    have hodd : Odd (2 * j + 1) := ⟨j, by omega⟩
    have hexp : 2 * j + 1 + 2 = 2 * j + 3 := by omega
    rw [oddPart, if_pos hodd, hexp, pow_add, pow_mul]
    ring
  calc ∑' i : ℕ, oddPart i
      = ∑' j : ℕ, oddPart (2 * j + 1) := (hinj.tsum_eq hsupp).symm
    _ = ∑' j : ℕ, (-goldenConj) ^ 3 * (goldenConj ^ 2) ^ j := tsum_congr hval
    _ = (-goldenConj) ^ 3 * (-goldenConj)⁻¹ := by rw [tsum_mul_left, sq_geometric_tsum]
    _ = goldenConj ^ 2 := by
        have hcube : (-goldenConj) ^ 3 = goldenConj ^ 2 * -goldenConj := by ring
        rw [hcube, mul_inv_cancel_right₀ neg_goldenConj_ne_zero]

/-! ### The window bound

Any finite set of Zeckendorf indices evaluates on the contraction face inside
the window `[-psi ^ 2, -psi] = [-1 / phi ^ 2, 1 / phi]`: dropping the negative
odd-exponent terms bounds the sum above by the full even-exponent series, and
dropping the positive even-exponent terms bounds it below by the negated full
odd-exponent series. -/

private theorem sum_le_window (s : Finset ℕ) :
    ∑ i ∈ s, goldenConj ^ (i + 2) ≤ -goldenConj := by
  have hle : ∑ i ∈ s, goldenConj ^ (i + 2) ≤ ∑ i ∈ s, evenPart i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [evenPart]
    split
    · exact le_refl _
    · rename_i hev
      have hodd : Odd (i + 2) := by
        rw [Nat.odd_iff]
        have := Nat.even_iff.not.mp hev
        omega
      exact hodd.pow_nonpos goldenConj_nonpos
  have htsum : ∑ i ∈ s, evenPart i ≤ ∑' i : ℕ, evenPart i :=
    evenPart_summable.sum_le_tsum s fun i _ => evenPart_nonneg i
  calc ∑ i ∈ s, goldenConj ^ (i + 2)
      ≤ ∑ i ∈ s, evenPart i := hle
    _ ≤ ∑' i : ℕ, evenPart i := htsum
    _ = -goldenConj := evenPart_tsum

private theorem window_le_sum (s : Finset ℕ) :
    -(goldenConj ^ 2) ≤ ∑ i ∈ s, goldenConj ^ (i + 2) := by
  have hle : ∑ i ∈ s, -goldenConj ^ (i + 2) ≤ ∑ i ∈ s, oddPart i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [oddPart]
    split
    · exact le_refl _
    · rename_i hodd
      have hev : Even (i + 2) := by
        rw [Nat.even_iff]
        have := Nat.odd_iff.not.mp hodd
        omega
      have := hev.pow_nonneg goldenConj
      linarith
  have htsum : ∑ i ∈ s, oddPart i ≤ ∑' i : ℕ, oddPart i :=
    oddPart_summable.sum_le_tsum s fun i _ => oddPart_nonneg i
  have hneg : ∑ i ∈ s, -goldenConj ^ (i + 2) = -∑ i ∈ s, goldenConj ^ (i + 2) := by
    simp
  have hbound : -∑ i ∈ s, goldenConj ^ (i + 2) ≤ goldenConj ^ 2 := by
    calc -∑ i ∈ s, goldenConj ^ (i + 2)
        = ∑ i ∈ s, -goldenConj ^ (i + 2) := hneg.symm
      _ ≤ ∑ i ∈ s, oddPart i := hle
      _ ≤ ∑' i : ℕ, oddPart i := htsum
      _ = goldenConj ^ 2 := oddPart_tsum
  linarith

/-! ### The contraction face as a psi-power sum over canonical digits -/

private theorem conj_natCast (n : ℕ) : conj (n : GoldenInt) = (n : GoldenInt) := by
  apply GoldenInt.ext <;> simp

private theorem betaContraction_eq_sum (v : ℕ) :
    betaContraction v = ∑ i ∈ (toRaw (Z v)).support, goldenConj ^ (i + 2) := by
  classical
  have hcanon := canonicalRaw_toRaw (Z v)
  rw [betaContraction, betaGolden, betaDigits, Finsupp.sum]
  have hconj : conj (∑ i ∈ (toRaw (Z v)).support,
      ((toRaw (Z v)) i : GoldenInt) * phi ^ (i + 2))
      = ∑ i ∈ (toRaw (Z v)).support,
        conj (((toRaw (Z v)) i : GoldenInt) * phi ^ (i + 2)) :=
    map_sum conjEquiv _ _
  rw [hconj, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hone : (toRaw (Z v)) i = 1 :=
    le_antisymm (hcanon.1 i)
      (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have hconjpow : conj (phi ^ (i + 2)) = (1 - phi) ^ (i + 2) := by
    calc conj (phi ^ (i + 2))
        = conjEquiv (phi ^ (i + 2)) := rfl
      _ = conjEquiv phi ^ (i + 2) := map_pow _ _ _
      _ = (1 - phi) ^ (i + 2) := by
          rw [show conjEquiv phi = conj phi from rfl, conj_phi]
  rw [conj_mul, conj_natCast, hconjpow, hone]
  have hpsi : embedding (1 - phi) = goldenConj := by
    rw [map_sub, map_one, embedding_phi, Real.one_sub_goldenConj]
  rw [map_mul, map_pow, hpsi, map_natCast]
  norm_num

/-! ### The three-valued deficit theorem

The three-valued deficit theorem: the normalized beta deficit of golden
addition takes only
the three values `-1`, `0`, and `1`.  Each contraction-face reading lands in
the window `[-1 / phi ^ 2, 1 / phi]`, so the deficit lies strictly between
`-2` and `2`; the integer certificate of `deficit_integer` then pins it to
the three central integers.  The final numeric gates are exactly
`-(2 + psi) > -2` and `1 - psi = phi < 2`: the window of length one admits
precisely three integers. -/

theorem deficit_three_valued (v₁ v₂ : ℕ) :
    deficit v₁ v₂ = -1 ∨ deficit v₁ v₂ = 0 ∨ deficit v₁ v₂ = 1 := by
  obtain ⟨hface, ⟨z, hz⟩, -⟩ := deficit_integer v₁ v₂
  have hwin : ∀ v : ℕ,
      -(goldenConj ^ 2) ≤ betaContraction v ∧ betaContraction v ≤ -goldenConj := by
    intro v
    rw [betaContraction_eq_sum v]
    exact ⟨window_le_sum _, sum_le_window _⟩
  have hc : deficit v₁ v₂
      = betaContraction v₁ + betaContraction v₂ - betaContraction (v₁ + v₂) := by
    rw [hface, deficitContraction]
  obtain ⟨hl₁, hu₁⟩ := hwin v₁
  obtain ⟨hl₂, hu₂⟩ := hwin v₂
  obtain ⟨hl₃, hu₃⟩ := hwin (v₁ + v₂)
  have hψneg : goldenConj < 0 := goldenConj_neg
  have hψlow : (-1 : ℝ) < goldenConj := neg_one_lt_goldenConj
  have hψsq : goldenConj ^ 2 = goldenConj + 1 := goldenConj_sq
  have hlower : (-2 : ℝ) < deficit v₁ v₂ := by rw [hc]; linarith
  have hupper : deficit v₁ v₂ < 2 := by rw [hc]; linarith
  rw [hz] at hlower hupper
  have hzl : (-2 : ℤ) < z := by exact_mod_cast hlower
  have hzu : z < 2 := by exact_mod_cast hupper
  have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hcases with h | h | h
  · left; rw [hz, h]; norm_num
  · right; left; rw [hz, h]; norm_num
  · right; right; rw [hz, h]; norm_num

end D5.S1.Deficit
