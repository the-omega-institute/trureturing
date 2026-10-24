/- GID: D5/S3/Analytic/KarpZhangGamma/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired gamma kernels give coefficientwise positivity of the two-variable transform. -/

import D5.S3.Analytic.KarpZhangGamma.Kernel

/-!
admission_basis: escape-witness
content theorem: pairedKernel_sign, consumed by two_variable_nonneg.
escape_witness: The Gamma recurrence and increasing increments of (x-1)/(S-x) give the
backward step for the four-term bracket. pairedKernel_sign inductively
propagates nonpositivity across arbitrary index gaps, contradicting an
earlier positive entry. Pairing counts the middle term once. The nonnegative
total and increasing smoothed weights prove two_variable_nonneg.
The gamma-series identification is supplied by Series, not this module.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* pairedKernel: proof_shape: definition; escape_witness: none;
  consumers: finite_pairing, pairedKernel_bracket, pairedKernel_sign, pairedKernel_sum_nonneg, two_variable_nonneg.
* reciprocalPair: proof_shape: definition; escape_witness: none;
  consumers: fourBracket, fourBracket_backward, fourBracket_swap, pairedKernel_bracket, reciprocalPair_balanced, reciprocalPair_step.
* fourBracket: proof_shape: definition; escape_witness: none;
  consumers: bracket_backward_nat, fourBracket_backward, fourBracket_swap, pairedKernel_bracket, pairedKernel_sign.
* reciprocalPair_balanced: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* reciprocalPair_step: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* recurrenceFactor: proof_shape: definition; escape_witness: none;
  consumers: fourBracket_backward, recurrenceFactor_increment, recurrenceFactor_mono.
* recurrenceFactor_mono: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* recurrenceFactor_increment: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* fourBracket_backward: proof_shape: bind-only; escape_witness: none;
  consumers: bracket_backward_nat.
* fourBracket_swap: proof_shape: bind-only; escape_witness: none;
  consumers: bracket_backward_nat.
* bracket_backward_nat: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sign.
* pairedKernel_bracket: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sign.
* pairedKernel_sign: proof_shape: content; escape_witness: pairedKernel_sign;
  consumers: two_variable_nonneg.
* pair_sum: proof_shape: bind-only; escape_witness: none;
  consumers: finite_pairing.
* finite_pairing: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sum_nonneg, two_variable_nonneg.
* pairedKernel_sum_nonneg: proof_shape: content; escape_witness: KarpZhangGamma.Kernel.binomialGamma_sum;
  consumers: two_variable_nonneg.
* transformDelta: proof_shape: definition; escape_witness: none;
  consumers: two_variable_nonneg, KarpZhangGamma.Series.gamma_half, KarpZhangGamma.Series.transformed_delta.
* two_variable_nonneg: proof_shape: content; escape_witness: pairedKernel_sign;
  consumers: KarpZhangGamma.Series.gamma_half.

Direct frozen D5 dependencies: none; all KarpZhang dependencies are
same-delivery declarations. Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Analytic.KarpZhangGamma.Result

open Smoothing Kernel

/-- The paired kernel counts the middle index only once. -/
def pairedKernel (a α β : ℝ) (m k : ℕ) : ℝ :=
  if 2 * k < m then kernel a α β m k + kernel a α β m (m - k)
  else kernel a α β m k

private def reciprocalPair (x z : ℝ) : ℝ :=
  1 / (Real.Gamma x * Real.Gamma z)

private def fourBracket (x z α β : ℝ) : ℝ :=
  reciprocalPair (x + α) (z + β) + reciprocalPair (x + β) (z + α) -
    reciprocalPair x (z + α + β) - reciprocalPair (x + α + β) z

private theorem reciprocalPair_balanced (x α β : ℝ) (hx : 0 < x)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    reciprocalPair x (x + α + β) ≤ reciprocalPair (x + α) (x + β) := by
  exact one_div_le_one_div_of_le
    (mul_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos (by linarith))) (gamma_balanced_shift x α β hx hα hβ)

private theorem reciprocalPair_step (x z : ℝ) (hx : 1 < x) (hz : 0 < z) :
    reciprocalPair (x - 1) (z + 1) = reciprocalPair x z * ((x - 1) / z) := by
  have hΓ : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
    convert Real.Gamma_add_one (show x - 1 ≠ 0 by linarith) using 1 <;> ring
  unfold reciprocalPair
  rw [hΓ, Real.Gamma_add_one (ne_of_gt hz)]
  field_simp [ne_of_gt hz, show x - 1 ≠ 0 by linarith,
    ne_of_gt (Real.Gamma_pos_of_pos (show 0 < x - 1 by linarith)),
    ne_of_gt (Real.Gamma_pos_of_pos hz)]
  <;> ring

private def recurrenceFactor (S x : ℝ) : ℝ := (x - 1) / (S - x)

private theorem recurrenceFactor_mono (S x z : ℝ) (hS : 1 ≤ S)
    (hxz : x ≤ z) (hz : z < S) : recurrenceFactor S x ≤ recurrenceFactor S z := by
  unfold recurrenceFactor
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hxz) (sub_nonneg.mpr hS)]

private theorem recurrenceFactor_increment (S x α β : ℝ) (hS : 1 ≤ S)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hd : x + α + β < S) :
    recurrenceFactor S (x + β) - recurrenceFactor S x ≤
      recurrenceFactor S (x + α + β) - recurrenceFactor S (x + α) := by
  have hd0 : 0 < S - (x + α + β) := by linarith
  have hd1 : 0 < S - (x + α) := by linarith
  have hd2 : 0 < S - (x + β) := by linarith
  have hd3 : 0 < S - x := by linarith
  have hfirst : recurrenceFactor S (x + β) - recurrenceFactor S x =
      β * (S - 1) / ((S - (x + β)) * (S - x)) := by
    unfold recurrenceFactor
    field_simp [ne_of_gt hd2, ne_of_gt hd3]
    <;> ring
  have hsecond : recurrenceFactor S (x + α + β) - recurrenceFactor S (x + α) =
      β * (S - 1) / ((S - (x + α + β)) * (S - (x + α))) := by
    unfold recurrenceFactor
    field_simp [ne_of_gt hd0, ne_of_gt hd1]
    <;> ring
  have hden : (S - (x + α + β)) * (S - (x + α)) ≤
      (S - (x + β)) * (S - x) :=
    mul_le_mul (by linarith) (by linarith) (le_of_lt hd1) (le_of_lt hd2)
  rw [hfirst, hsecond, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hd0 hd1) hden)
    (mul_nonneg hβ (sub_nonneg.mpr hS))

/-- Backward propagation of a nonpositive four-term bracket. The recurrence
factor has increasing increments; no differentiability of Gamma is needed. -/
private theorem fourBracket_backward (x z α β : ℝ) (hx : 1 < x) (hxz : x ≤ z)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hB : fourBracket x z α β ≤ 0) :
    fourBracket (x - 1) (z + 1) α β ≤ 0 := by
  let S := x + z + α + β
  let u := reciprocalPair (x + α) (z + β)
  let v := reciprocalPair (x + β) (z + α)
  let r := reciprocalPair x (z + α + β)
  let s := reciprocalPair (x + α + β) z
  have hβ : 0 ≤ β := hα.trans hαβ
  have hz : 0 < z := by linarith
  have hru : r ≤ u := by
    have h := reciprocalPair_balanced x α (z - x + β) (by linarith) hα
      (by linarith)
    change reciprocalPair x (z + α + β) ≤ reciprocalPair (x + α) (z + β)
    simpa only [show x + α + (z - x + β) = z + α + β by ring,
      show x + (z - x + β) = z + β by ring] using h
  have huv : u ≤ v := by
    have h := reciprocalPair_balanced (x + α) (β - α) (z - x)
      (by linarith) (by linarith) (by linarith)
    change reciprocalPair (x + α) (z + β) ≤ reciprocalPair (x + β) (z + α)
    rw [show x + α + (β - α) + (z - x) = z + β by ring,
      show x + α + (β - α) = x + β by ring,
      show x + α + (z - x) = z + α by ring] at h
    exact h
  have hs : 0 ≤ s := by
    dsimp [s, reciprocalPair]
    exact le_of_lt (one_div_pos.mpr (mul_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos hz)))
  have hvs : v ≤ s := by dsimp [fourBracket] at hB; dsimp [u, v, r, s] at *; linarith
  have hrs : r ≤ s := hru.trans (huv.trans hvs)
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hd : x + α + β < S := by dsimp [S]; linarith
  have hbc := recurrenceFactor_mono S (x + α) (x + β) hS (by linarith)
    (by linarith)
  have hab := recurrenceFactor_mono S x (x + α) hS (by linarith) (by linarith)
  have hb0 : 0 ≤ recurrenceFactor S (x + α) := by
    dsimp [recurrenceFactor]
    exact div_nonneg (by linarith) (by linarith)
  have hconv := recurrenceFactor_increment S x α β hS hα hβ hd
  have hu : reciprocalPair (x - 1 + α) (z + 1 + β) =
      u * recurrenceFactor S (x + α) := by
    have h := reciprocalPair_step (x + α) (z + β) (by linarith) (by linarith)
    dsimp [u, recurrenceFactor]
    rw [show S - (x + α) = z + β by dsimp [S]; ring]
    simpa only [show x + α - 1 = x - 1 + α by ring,
      show z + β + 1 = z + 1 + β by ring] using h
  have hv : reciprocalPair (x - 1 + β) (z + 1 + α) =
      v * recurrenceFactor S (x + β) := by
    have h := reciprocalPair_step (x + β) (z + α) (by linarith) (by linarith)
    dsimp [v, recurrenceFactor]
    rw [show S - (x + β) = z + α by dsimp [S]; ring]
    simpa only [show x + β - 1 = x - 1 + β by ring,
      show z + α + 1 = z + 1 + α by ring] using h
  have hr : reciprocalPair (x - 1) (z + 1 + α + β) =
      r * recurrenceFactor S x := by
    have h := reciprocalPair_step x (z + α + β) hx (by linarith)
    dsimp [r, recurrenceFactor]
    rw [show S - x = z + α + β by dsimp [S]; ring]
    simpa only [show z + α + β + 1 = z + 1 + α + β by ring] using h
  have ht : reciprocalPair (x - 1 + α + β) (z + 1) =
      s * recurrenceFactor S (x + α + β) := by
    have h := reciprocalPair_step (x + α + β) z (by linarith) hz
    dsimp [s, recurrenceFactor]
    rw [show S - (x + α + β) = z by dsimp [S]; ring]
    simpa only [show x + α + β - 1 = x - 1 + α + β by ring] using h
  have hterm := mul_nonpos_of_nonneg_of_nonpos hb0 hB
  have hvterm := mul_le_mul_of_nonneg_right hvs (sub_nonneg.mpr hbc)
  have hrterm := mul_le_mul_of_nonneg_right hrs (sub_nonneg.mpr hab)
  have hlast := mul_nonpos_of_nonneg_of_nonpos hs
    (show (recurrenceFactor S (x + β) - recurrenceFactor S x) -
      (recurrenceFactor S (x + α + β) - recurrenceFactor S (x + α)) ≤ 0 by linarith)
  change u + v - r - s ≤ 0 at hB
  change recurrenceFactor S (x + α) * (u + v - r - s) ≤ 0 at hterm
  unfold fourBracket
  rw [hu, hv, hr, ht]
  nlinarith

private theorem fourBracket_swap (x z α β : ℝ) :
    fourBracket x z α β = fourBracket x z β α := by
  unfold fourBracket
  rw [show z + α + β = z + β + α by ring,
    show x + α + β = x + β + α by ring]
  ring

private theorem bracket_backward_nat (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (m k : ℕ) (hk : k + 1 ≤ m / 2)
    (hB : fourBracket (a + (k + 1 : ℕ)) (a + (m - (k + 1))) α β ≤ 0) :
    fourBracket (a + k) (a + (m - k)) α β ≤ 0 := by
  have hstep (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β)
      (h : fourBracket (a + (k + 1 : ℕ)) (a + (m - (k + 1))) α β ≤ 0) :
      fourBracket (a + k) (a + (m - k)) α β ≤ 0 := by
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
    have horder : k + 1 ≤ m - (k + 1) := by omega
    have horder' : ((k + 1 : ℕ) : ℝ) ≤ ((m - (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast horder
    rw [Nat.cast_sub (by omega : k + 1 ≤ m), hcast] at horder'
    have h := fourBracket_backward (a + (k + 1 : ℕ))
      (a + (m - (k + 1))) α β (by
        rw [hcast]
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith)
      (by rw [hcast]; linarith only [horder']) hα hαβ h
    have hxarg : a + ((k + 1 : ℕ) : ℝ) - 1 = a + k := by rw [hcast]; ring
    have hzarg : a + ((m : ℝ) - ((k : ℝ) + 1)) + 1 = a + (m - k) := by ring
    rwa [hxarg, hzarg] at h
  by_cases hab : α ≤ β
  · exact hstep α β hα hab hB
  · rw [fourBracket_swap] at hB ⊢
    exact hstep β α hβ (le_of_not_ge hab) hB

private theorem pairedKernel_bracket (a α β : ℝ) (m k : ℕ) (hk : k ≤ m / 2) :
    pairedKernel a α β m k =
      fourBracket (a + k) (a + (m - k)) α β /
        (if 2 * k < m then (k.factorial : ℝ) * ((m - k).factorial : ℝ)
         else 2 * (k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
  have hmk : m - (m - k) = k := by omega
  have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  unfold pairedKernel kernel fourBracket reciprocalPair
  split_ifs with h
  · rw [hmk, hcast, show (m : ℝ) - ((m : ℝ) - (k : ℝ)) = k by ring]
    simp only [add_assoc, add_left_comm, add_comm, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  · have hmid : m - k = k := by omega
    have hmid' : (m : ℝ) - (k : ℝ) = k := by rw [← hcast, hmid]
    rw [hmid, hmid']
    simp only [add_assoc, add_left_comm, add_comm, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring

/-- Lemma 4's weak sign pattern, including zero shifts: a positive paired
entry cannot be followed by a negative paired entry. -/
theorem pairedKernel_sign (a α β : ℝ) (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (m : ℕ) : ∀ i ≤ m / 2, ∀ j ≤ m / 2, i < j →
      0 < pairedKernel a α β m i → 0 ≤ pairedKernel a α β m j := by
  intro i hi j hj hij hpos
  have hden (k : ℕ) : 0 <
      (if 2 * k < m then (k.factorial : ℝ) * ((m - k).factorial : ℝ)
       else 2 * (k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
    split_ifs <;> positivity
  rw [pairedKernel_bracket a α β m i hi] at hpos
  have hBi : 0 < fourBracket (a + i) (a + (m - i)) α β :=
    (div_pos_iff_of_pos_right (hden i)).mp hpos
  rw [pairedKernel_bracket a α β m j hj]
  apply div_nonneg _ (le_of_lt (hden j))
  by_contra hn
  have hBj : fourBracket (a + j) (a + (m - j)) α β ≤ 0 := le_of_lt (lt_of_not_ge hn)
  have hprop : ∀ d, i + d ≤ m / 2 →
      fourBracket (a + (i + d : ℕ)) (a + (m - (i + d : ℕ))) α β ≤ 0 →
      fourBracket (a + i) (a + (m - i)) α β ≤ 0 := by
    intro d
    induction d with
    | zero => intro _ h; simpa only [Nat.add_zero] using h
    | succ d ih =>
      intro hd h
      apply ih (by omega)
      apply bracket_backward_nat a α β ha hα hβ m (i + d) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h
  have h := hprop (j - i) (by omega) (by simpa only [show i + (j - i) = j by omega] using hBj)
  exact (not_le_of_gt hBi) h

private theorem pair_sum (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (m + 1), f k) = ∑ k ∈ range (m / 2 + 1),
      if 2 * k < m then f k + f (m - k) else f k := by
  classical
  have hlow : (range (m + 1)).filter (fun k => 2 * k ≤ m) = range (m / 2 + 1) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  have hhigh : (∑ k ∈ (range (m + 1)).filter (fun k => ¬ 2 * k ≤ m), f k) =
      ∑ k ∈ (range (m / 2 + 1)).filter (fun k => 2 * k < m), f (m - k) := by
    apply sum_bij (fun k _ => m - k)
    · intro k hk
      simp only [mem_filter, mem_range] at hk ⊢
      omega
    · intro k hk l hl hkl
      simp only [mem_filter, mem_range] at hk hl
      omega
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      refine ⟨m - k, ?_, ?_⟩
      · simp only [mem_filter, mem_range]
        omega
      · omega
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      congr 1
      omega
  rw [← sum_filter_add_sum_filter_not (range (m + 1)) (fun k => 2 * k ≤ m) f,
    hlow, hhigh, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  split_ifs <;> ring

/-- Exact finite pairing for any symmetric weights; a middle term is not doubled. -/
theorem finite_pairing (a α β : ℝ) (m : ℕ) (W : ℕ → ℝ)
    (hsym : ∀ k ≤ m, W (m - k) = W k) :
    (∑ k ∈ range (m + 1), kernel a α β m k * W k) =
      ∑ k ∈ range (m / 2 + 1), pairedKernel a α β m k * W k := by
  rw [pair_sum]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := mem_range.mp hk; omega
  unfold pairedKernel
  split_ifs with h
  · rw [hsym k hkm]
    ring
  · rfl

/-- The paired scalar kernel has the same nonnegative total as the unpaired kernel. -/
theorem pairedKernel_sum_nonneg (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (m : ℕ) :
    0 ≤ ∑ k ∈ range (m / 2 + 1), pairedKernel a α β m k := by
  have h := finite_pairing a α β m (fun _ => 1) (by intros; rfl)
  simp only [mul_one] at h
  rw [← h]
  exact kernel_sum_nonneg a α β ha hα hβ m

/-- The degree-(N,m) coefficient of the Turanian of the two-variable
transform H(a;z,w), written with finite Cauchy sums. -/
def transformDelta (y : ℕ → ℝ) (a α β : ℝ) (N m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), kernel a α β m k *
    productCoeff (fun r => y (2 * k + r)) (fun r => y (2 * (m - k) + r)) N

/-- Theorem 5 in coefficient form, for every bidegree and arbitrary
nonnegative real shifts, with no growth or convergence assumption. -/
theorem two_variable_nonneg (y : ℕ → ℝ)
    (hy : D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave y)
    (a α β : ℝ) (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β) (N m : ℕ) :
    0 ≤ transformDelta y a α β N m := by
  have hcomm (f g : ℕ → ℝ) : productCoeff f g N = productCoeff g f N := by
    rw [productCoeff_eq, productCoeff_eq, binomialProduct_comm]
  unfold transformDelta
  rw [finite_pairing a α β m _ (by
    intro k hk
    rw [show m - (m - k) = k by omega]
    exact hcomm _ _)]
  exact smoothed_weighting hy (pairedKernel a α β m) m
    (pairedKernel_sign a α β ha hα hβ m)
    (pairedKernel_sum_nonneg a α β ha hα hβ m) N


end D5.S3.Analytic.KarpZhangGamma.Result
