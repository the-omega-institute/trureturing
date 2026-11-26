/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact identification of the degree-seventeen polynomial with the spectral kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusAllocation
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumCounts

/-! The executable recurrence computes the complete homogeneous sum in the
four slots of the spectral deficit. -/

namespace RefinedBMV.Tracial.TriangleSurplus

open scoped BigOperators
open FourCopyGap ThreeBlockGram
open DividedDifference (homogeneousTwo homogeneousThree)
open private balanced from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private sum_gaps_first from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumCounts

private def atCoeff {R : Type*} [Zero R] (row : List R) (n : ℕ) : R :=
  row[n]?.getD 0

@[simp] private theorem adjoin_length {R : Type*} [Add R] [Mul R] (x prev : R)
    (row : List R) : (adjoin x prev row).length = row.length := by
  induction row generalizing prev with
  | nil => rfl
  | cons a as ih => simp [adjoin, ih]

private theorem adjoin_at {R : Type*} [CommRing R] (x prev : R) (row : List R)
    (n : ℕ) (hn : n < row.length) :
    atCoeff (adjoin x prev row) n =
      (∑ j ∈ Finset.range (n+1), x ^ j * atCoeff row (n-j)) + x ^ (n+1) * prev := by
  induction row generalizing prev n with
  | nil => simp at hn
  | cons a as ih =>
    cases n with
    | zero =>
      simp [adjoin, atCoeff]
    | succ n =>
      have hn' : n < as.length := by simpa using hn
      change atCoeff (adjoin x (a + x * prev) as) n = _
      rw [ih _ _ hn', Finset.sum_range_succ _ (n+1)]
      have hsum :
          (∑ j ∈ Finset.range (n+1), x ^ j * atCoeff (a :: as) (n+1-j)) =
            ∑ j ∈ Finset.range (n+1), x ^ j * atCoeff as (n-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show n+1-j = (n-j)+1 by have := Finset.mem_range.mp hj; omega]
        rfl
      rw [hsum, Nat.sub_self]
      change _ = _ + x ^ (n+1) * a + _
      rw [pow_succ]
      ring

private theorem initial_at {R : Type*} [CommRing R] (x : R) (n : ℕ)
    (hn : n ≤ 17) :
    atCoeff (adjoin x 0 ((1 : R) :: List.replicate 17 0)) n = x ^ n := by
  rw [adjoin_at x 0 _ n (by simpa using Nat.lt_succ_of_le hn), mul_zero, add_zero]
  rw [Finset.sum_eq_single n]
  · simp [atCoeff]
  · intro j hj hjn
    have hjle := Finset.mem_range.mp hj
    have hdiff : 0 < n-j := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-j ≠ 0)
    simp only [atCoeff, hk, List.getElem?_cons_succ, List.getElem?_replicate]
    split <;> simp
  · simp

private theorem extend_eq_adjoin {R : Type*} [CommRing R] (x : R) (row : List R) :
    extend x row = adjoin x 0 row := by
  cases row <;> simp [extend, adjoin]

private theorem gap_reversed {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    gap a b c d = gapDefect 17 (d ^ 4) (c ^ 4) (b ^ 4) (a ^ 4) := by
  let A := a ^ (4 : ℕ)
  let B := b ^ (4 : ℕ)
  let C := c ^ (4 : ℕ)
  let D := d ^ (4 : ℕ)
  let ra : List ℝ := adjoin A 0 (1 :: List.replicate 17 0)
  let rb := adjoin B 0 ra
  let rc := adjoin C 0 rb
  let rd := adjoin D 0 rc
  have hA (n : ℕ) (hn : n ≤ 17) : atCoeff ra n = A ^ n :=
    initial_at A n hn
  have hB (n : ℕ) (hn : n ≤ 17) : atCoeff rb n = homogeneousTwo n B A := by
    rw [show rb = adjoin B 0 ra from rfl,
      adjoin_at B 0 ra n (by simpa [ra] using Nat.lt_succ_of_le hn), mul_zero, add_zero]
    unfold homogeneousTwo
    exact Finset.sum_congr rfl fun j _ => by rw [hA _ (by omega)]
  have hC (n : ℕ) (hn : n ≤ 17) : atCoeff rc n = homogeneousThree n C B A := by
    rw [show rc = adjoin C 0 rb from rfl,
      adjoin_at C 0 rb n (by simpa [rb, ra] using Nat.lt_succ_of_le hn), mul_zero, add_zero]
    unfold homogeneousThree
    exact Finset.sum_congr rfl fun j _ => by rw [hB _ (by omega)]
  have hD : atCoeff rd 17 = ∑ j ∈ Finset.range 18, D ^ j * homogeneousThree (17-j) C B A := by
    rw [show rd = adjoin D 0 rc from rfl,
      adjoin_at D 0 rc 17 (by simp [rc, rb, ra]), mul_zero, add_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [hC _ (by omega)]
  have hr (x : ℝ) (hx : 0 ≤ x) : (x ^ (4 : ℕ)) ^ ((17 : ℝ) / 4) = x ^ (17 : ℕ) := by
    rw [← Real.rpow_natCast_mul hx, show ↑(4 : ℕ) * ((17 : ℝ) / 4) = (17 : ℝ) by norm_num]
    exact Real.rpow_natCast x 17
  have hcard : (gaps 17).card = 1140 := by rw [gaps_card]; decide +kernel
  simp only [gap, extend_eq_adjoin, Nat.cast_one, Nat.cast_zero]
  change atCoeff rd 17 - (↑(1140 : ℕ) : ℝ) * (a*b*c*d) ^ (17 : ℕ) = _
  rw [gapDefect, sum_gaps_first, hcard, hD]
  simp only [balanced, Nat.cast_ofNat, hr a ha, hr b hb, hr c hc, hr d hd, mul_pow]
  ring

/-- The polynomial arithmetic agrees with the spectral deficit at nonnegative
fourth powers, including zero. -/
theorem gap_eq_gapDefect {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    gap a b c d = gapDefect 17 (a ^ 4) (b ^ 4) (c ^ 4) (d ^ 4) := by
  rw [gap_reversed ha hb hc hd]
  rw [gapDefect_swap01 17 (d^4) (c^4) (b^4) (a^4),
    gapDefect_swap12 17 (c^4) (d^4) (b^4) (a^4),
    gapDefect_swap23 17 (c^4) (b^4) (d^4) (a^4),
    gapDefect_swap01 17 (c^4) (b^4) (a^4) (d^4),
    gapDefect_swap12 17 (b^4) (c^4) (a^4) (d^4),
    gapDefect_swap01 17 (b^4) (a^4) (c^4) (d^4)]

/-- The computed surpluses use the same edge and vertex weights as the
spectral triangle allocation. -/
theorem surplus_eq_kernelSurplus {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    surplus x y =
      kernelSurplus (spectralDefect 17 ![1, x ^ 4, (x * y) ^ 4]) ![4, 4, 3 + y ^ 17] := by
  have hxy := mul_nonneg hx hy
  simp only [surplus, Nat.cast_one, Nat.cast_ofNat]
  simp (disch := first | assumption | positivity) only [gap_eq_gapDefect, one_pow]
  simp [kernelSurplus, kernelEdge, triangleDemand, f, g, h, spectralDefect]

#print axioms surplus_eq_kernelSurplus

end RefinedBMV.Tracial.TriangleSurplus
