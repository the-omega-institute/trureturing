/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumCounts
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral word counts for the singular three-value allocation. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGramFiniteSums
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumFormulas
import D5.S3.Quantum.Analysis.RefinedBMVUniformDiscriminant
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Exact counts of the weak compositions contributing to the singular kernel. -/

noncomputable section

open scoped BigOperators

namespace RefinedBMV.ThreeBlockGram.ZeroSpectrum

open FourCopyGap
open Separated (rawS rawU rawV rawF rawG rawW)
open DividedDifference (homogeneousTwo homogeneousThree)
open private monomial balanced from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private homogeneousTwo_diag from D5.S3.Quantum.Analysis.RefinedBMVUniformDiscriminant

private theorem sum_gaps_first (p : ℕ) (a b c d : ℝ) :
    (∑ g ∈ gaps p, monomial a b c d g) =
      ∑ i ∈ Finset.range (p + 1), a^i * homogeneousThree (p-i) b c d := by
  let indices : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
    (Finset.range (p+1)).sigma fun i ↦
      (Finset.range (p-i+1)).sigma fun j ↦ Finset.range (p-i-j+1)
  let encode (g : Gap) : Σ _ : ℕ, Σ _ : ℕ, ℕ := ⟨g.1, g.2.1, g.2.2.1⟩
  let decode (x : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Gap :=
    (x.1, x.2.1, x.2.2, p - x.1 - x.2.1 - x.2.2)
  calc
    _ = ∑ x ∈ indices, a^x.1 * (b^x.2.1 * (c^x.2.2 * d^(p-x.1-x.2.1-x.2.2))) := by
      apply Finset.sum_nbij' encode decode
      · intro g hg
        simp only [mem_gaps] at hg
        simp only [indices, Finset.mem_sigma, Finset.mem_range, encode]
        omega
      · intro x hx
        simp only [indices, Finset.mem_sigma, Finset.mem_range] at hx
        simp only [mem_gaps, decode]
        omega
      · rintro ⟨i,j,k,l⟩ hx
        simp only [mem_gaps] at hx
        have hl : p-i-j-k = l := by omega
        simp only [encode, decode, hl]
      · rintro ⟨i,j,k⟩ _
        rfl
      · rintro ⟨i,j,k,l⟩ hx
        simp only [mem_gaps] at hx
        have hl : p-i-j-k = l := by omega
        simp only [encode, monomial, hl, mul_assoc]
    _ = _ := by
      simp only [indices, Finset.sum_sigma, homogeneousThree, homogeneousTwo, Finset.mul_sum]

private theorem sum_gaps_pair (p : ℕ) (r : ℝ) :
    (∑ g ∈ gaps p, monomial r r 1 1 g) = rawW (p+1) r := by
  let indices : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
    (Finset.range (p+1)).sigma fun l ↦
      (Finset.range (l+1)).sigma fun _ ↦ Finset.range (p-l+1)
  let encode (g : Gap) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
    ⟨g.1 + g.2.1, g.1, g.2.2.1⟩
  let decode (x : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Gap :=
    (x.2.1, x.1-x.2.1, x.2.2, p-x.1-x.2.2)
  calc
    _ = ∑ x ∈ indices, r^x.1 := by
      apply Finset.sum_nbij' encode decode
      · intro g hg
        simp only [mem_gaps] at hg
        simp only [indices, Finset.mem_sigma, Finset.mem_range, encode]
        omega
      · intro x hx
        simp only [indices, Finset.mem_sigma, Finset.mem_range] at hx
        simp only [mem_gaps, decode]
        omega
      · rintro ⟨i,j,k,l⟩ hx
        simp only [mem_gaps] at hx
        have hl : p-(i+j)-k = l := by omega
        simp [decode, encode, hl]
      · rintro ⟨l,i,k⟩ hx
        simp only [indices, Finset.mem_sigma, Finset.mem_range] at hx
        have hl : i + (l-i) = l := by omega
        simp only [encode, decode, hl]
      · intro g _
        simp only [monomial, one_pow, mul_one, ← pow_add, encode]
    _ = _ := by
      simp only [indices, Finset.sum_sigma, Finset.sum_const, nsmul_eq_mul, rawW]
      apply Finset.sum_congr rfl
      intro l hl
      have hle : l ≤ p := Finset.mem_range_succ_iff.mp hl
      simp only [Finset.card_sigma, Finset.card_range, Finset.sum_const,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hle]
      push_cast
      ring

private theorem triangle_count (p : ℕ) :
    (∑ j ∈ Finset.range (p+1), (((p-j : ℕ) : ℝ) + 1)) = C p := by
  induction p with
  | zero => norm_num [C, q]
  | succ p ih =>
    have hshift : (∑ j ∈ Finset.range (p+1), ((((p+1)-(j+1) : ℕ) : ℝ) + 1)) =
        ∑ j ∈ Finset.range (p+1), (((p-j : ℕ) : ℝ) + 1) := by
      simp only [Nat.add_sub_add_right]
    rw [Finset.sum_range_succ', hshift, ih]
    simp only [Nat.sub_zero]
    push_cast
    unfold C q
    ring

private theorem three_diag (p : ℕ) (r : ℝ) :
    homogeneousThree p r r r = C p * r^p := by
  unfold homogeneousThree
  calc
    _ = ∑ j ∈ Finset.range (p+1), (((p-j : ℕ) : ℝ) + 1) * r^p := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ p := Finset.mem_range_succ_iff.mp hi
      rw [homogeneousTwo_diag, mul_left_comm, ← pow_add, Nat.add_sub_of_le hi']
    _ = _ := by rw [← Finset.sum_mul, triangle_count p]

private theorem two_zero (p : ℕ) (r : ℝ) : homogeneousTwo p 0 r = r^p := by
  simp only [homogeneousTwo, Finset.sum_range_succ', pow_succ, zero_mul, mul_zero,
    Finset.sum_const_zero, pow_zero, one_mul, Nat.sub_zero, zero_add]

private theorem three_zero (p : ℕ) (r t : ℝ) :
    homogeneousThree p 0 r t = homogeneousTwo p r t := by
  simp only [homogeneousThree, Finset.sum_range_succ', pow_succ, zero_mul, mul_zero,
    Finset.sum_const_zero, pow_zero, one_mul, Nat.sub_zero, zero_add]

private theorem gap_zero (p : ℕ) (hp : 0 < p) (b c d : ℝ) :
    gapDefect p 0 b c d = homogeneousThree p b c d := by
  have hp' : (p : ℝ) / 4 ≠ 0 := by positivity
  rw [gapDefect, sum_gaps_first]
  simp only [balanced, Real.zero_rpow hp', zero_mul, mul_zero, sub_zero,
    Finset.sum_range_succ', pow_succ, zero_mul, Finset.sum_const_zero,
    pow_zero, one_mul, Nat.sub_zero, zero_add]

private theorem card_gaps_real (p : ℕ) : ((gaps p).card : ℝ) = N p := by
  have h₂ := Nat.add_one_mul_choose_eq (p+1) 1
  have h₃ := Nat.add_one_mul_choose_eq (p+2) 2
  simp only [Nat.choose_one_right] at h₂
  have h₂' : ((p:ℝ)+2)*((p:ℝ)+1) = ((p+2).choose 2 : ℝ)*2 := by
    exact_mod_cast h₂
  have h₃' : ((p:ℝ)+3)*((p+2).choose 2 : ℝ) = ((p+3).choose 3 : ℝ)*3 := by
    exact_mod_cast h₃
  rw [gaps_card]
  calc
    _ = ((p:ℝ)+3)*((p+2).choose 2 : ℝ)/3 := by linarith only [h₃']
    _ = ((p:ℝ)+3)*(((p:ℝ)+2)*((p:ℝ)+1)/2)/3 := by
      rw [show ((p+2).choose 2 : ℝ) = ((p:ℝ)+2)*((p:ℝ)+1)/2 by linarith only [h₂']]
    _ = N p := by unfold N q; ring

theorem root_pow_eight (p : ℕ) {r : ℝ} (hr : 0 ≤ r) : (root p r)^8 = r^p := by
  rw [root, ← Real.rpow_mul_natCast hr]
  rw [show (p:ℝ)/8*((8:ℕ):ℝ) = (p:ℝ) by push_cast; ring, Real.rpow_natCast]

private theorem root_sq (p : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (root p r)^2 = r ^ ((p : ℝ) / 4) := by
  rw [root, ← Real.rpow_mul_natCast hr]
  rw [show (p : ℝ) / 8 * ((2 : ℕ) : ℝ) = (p : ℝ) / 4 by push_cast; ring]

private theorem raw_r111 (p : ℕ) (r : ℝ) :
    (∑ g ∈ gaps p, monomial r 1 1 1 g) = rawG (p+1) r := by
  rw [sum_gaps_first]
  unfold rawG
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ p := Finset.mem_range_succ_iff.mp hi
  rw [three_diag, one_pow]
  simp only [C, q, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
  ring

private theorem raw_1rrr (p : ℕ) (r : ℝ) :
    (∑ g ∈ gaps p, monomial 1 r r r g) = rawF (p+1) r := by
  rw [sum_gaps_first]
  simp only [one_pow, one_mul, three_diag]
  unfold rawF
  rw [← Finset.sum_range_reflect (fun i ↦ ((i:ℝ)+1)*((i:ℝ)+2)/2*r^i) (p+1)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.add_sub_cancel, C, q]
  ring

private theorem gap_rrr0 (p : ℕ) (hp : 0 < p) (r : ℝ) :
    gapDefect p r r r 0 = C p * r^p := by
  rw [gapDefect_swap23 p r r r 0, gapDefect_swap12 p r r 0 r,
    gapDefect_swap01 p r 0 r r, gap_zero p hp, three_diag]

private theorem gap_rr01 (p : ℕ) (hp : 0 < p) (r : ℝ) :
    gapDefect p r r 0 1 = rawU (p+1) r := by
  rw [gapDefect_swap12 p r r 0 1, gapDefect_swap01 p r 0 r 1,
    gapDefect_swap23 p 0 r r 1, gapDefect_swap12 p 0 r 1 r, gap_zero p hp]
  simp only [homogeneousThree, one_pow, one_mul, homogeneousTwo_diag]
  unfold rawU
  rw [← Finset.sum_range_reflect (fun i ↦ ((i:ℝ)+1)*r^i) (p+1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_sub_cancel]

private theorem gap_110r (p : ℕ) (hp : 0 < p) (r : ℝ) :
    gapDefect p 1 1 0 r = rawV (p+1) r := by
  rw [gapDefect_swap12 p 1 1 0 r, gapDefect_swap01 p 1 0 1 r,
    gapDefect_swap23 p 0 1 1 r, gapDefect_swap12 p 0 1 r 1, gap_zero p hp]
  simp only [homogeneousThree, homogeneousTwo_diag, one_pow, mul_one, rawV]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ p := Finset.mem_range_succ_iff.mp hi
  simp only [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
  ring

/-- The oracle's coefficients in the four-slot kernel's unnormalized convention. -/
structure Coefficients (p : ℕ) (r y : ℝ) : Prop where
  f01 : f (spectralDefect p ![0,r,1]) 0 1 = y^8
  f10 : f (spectralDefect p ![0,r,1]) 1 0 = C p * y^8
  g01 : g (spectralDefect p ![0,r,1]) 0 1 = q p * y^8
  f02 : f (spectralDefect p ![0,r,1]) 0 2 = 1
  f20 : f (spectralDefect p ![0,r,1]) 2 0 = C p
  g02 : g (spectralDefect p ![0,r,1]) 0 2 = q p
  f12 : f (spectralDefect p ![0,r,1]) 1 2 = rawF (p+1) r - N p * y^6
  f21 : f (spectralDefect p ![0,r,1]) 2 1 = rawG (p+1) r - N p * y^2
  g12 : g (spectralDefect p ![0,r,1]) 1 2 = rawW (p+1) r - N p * y^4
  h0 : h (spectralDefect p ![0,r,1]) 0 1 2 = rawS (p+1) r
  h1 : h (spectralDefect p ![0,r,1]) 1 0 2 = rawU (p+1) r
  h2 : h (spectralDefect p ![0,r,1]) 2 0 1 = rawV (p+1) r

theorem coefficient_counts (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 ≤ r) :
    Coefficients p r (root p r) := by
  have hy := root_pow_eight p hr
  have hy₂ := root_sq p hr
  constructor
  · change gapDefect p 0 0 0 r = _
    rw [gap_zero p hp, three_zero, two_zero, hy]
  · change gapDefect p r r r 0 = _
    rw [gap_rrr0 p hp, hy]
  · change gapDefect p 0 0 r r = _
    rw [gap_zero p hp, three_zero, homogeneousTwo_diag, hy]
    simp [q]
  · change gapDefect p 0 0 0 1 = _
    rw [gap_zero p hp, three_zero, two_zero, one_pow]
  · change gapDefect p 1 1 1 0 = _
    rw [gap_rrr0 p hp, one_pow, mul_one]
  · change gapDefect p 0 0 1 1 = _
    rw [gap_zero p hp, three_zero, homogeneousTwo_diag, one_pow, mul_one]
    simp [q]
  · change gapDefect p r r r 1 = _
    rw [gapDefect_swap23 p r r r 1, gapDefect_swap12 p r r 1 r,
      gapDefect_swap01 p r 1 r r, gapDefect, raw_1rrr, card_gaps_real]
    simp only [balanced, Real.one_rpow, one_mul, ← hy₂] <;> ring
  · change gapDefect p 1 1 1 r = _
    rw [gapDefect_swap23 p 1 1 1 r, gapDefect_swap12 p 1 1 r 1,
      gapDefect_swap01 p 1 r 1 1, gapDefect, raw_r111, card_gaps_real]
    simp only [balanced, Real.one_rpow, mul_one, ← hy₂]
  · change gapDefect p r r 1 1 = _
    rw [gapDefect, sum_gaps_pair, card_gaps_real]
    simp only [balanced, Real.one_rpow, mul_one, ← hy₂] <;> ring
  · change gapDefect p 0 0 r 1 = _
    rw [gap_zero p hp, three_zero]
    simp [homogeneousTwo, rawS]
  · change gapDefect p r r 0 1 = _
    exact gap_rr01 p hp r
  · change gapDefect p 1 1 0 r = _
    exact gap_110r p hp r

end RefinedBMV.ThreeBlockGram.ZeroSpectrum
