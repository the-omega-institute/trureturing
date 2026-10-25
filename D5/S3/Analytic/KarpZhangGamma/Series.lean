/- GID: D5/S3/Analytic/KarpZhangGamma/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive diagonal transforms transfer kernel positivity to gamma-series Turanians. -/

import D5.S3.Analytic.KarpZhangGamma.Result

/-!
admission_basis: escape-witness
content theorem: positive_beta_transform, consumed through series_identification by gamma_half.
escape_witness: Strong induction carries the positive diagonal transformation simultaneously
for every positive real parameter. Gamma duplication supplies degree zero;
the Gamma recurrence supplies degree one and the two-step degree recurrence.
The finite fibers r+2j=n justify the diagonal Cauchy identities. Positive
scale products transfer Result.two_variable_nonneg to gamma_half.
There is no convergence or growth hypothesis.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* gammaCoeff: proof_shape: bind-only (definition); escape_witness: none;
  consumers: gammaCoeff_one, gammaCoeff_recurrence, gammaCoeff_zero, gammaDelta, gamma_half, positive_beta_transform, series_identification.
* scale: proof_shape: bind-only (definition); escape_witness: none;
  consumers: gammaCoeff_zero, gamma_half, positive_beta_transform, scale_neutral, scale_pos, scale_succ, series_identification.
* indices: proof_shape: bind-only (definition); escape_witness: none;
  consumers: diagonal, diagonal_eq, diagonal_jshift, diagonal_mul_left, diagonal_recurrence, diagonal_rshift, mem_indices.
* mem_indices: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_eq, diagonal_jshift, diagonal_recurrence, diagonal_rshift.
* diagonal: proof_shape: bind-only (definition); escape_witness: none;
  consumers: diagonal_eq, diagonal_jshift, diagonal_mul_left, diagonal_product, diagonal_recurrence, diagonal_rshift, positive_beta_transform, transformCoeff_diagonal, transformed_product.
* diagonal_eq: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_product, positive_beta_transform, transformCoeff_diagonal.
* diagonal_mul_left: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_recurrence.
* diagonal_rshift: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_recurrence.
* diagonal_jshift: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_recurrence.
* atom: proof_shape: bind-only (definition); escape_witness: none;
  consumers: atom_jshift, atom_product, atom_rshift, diagonal_recurrence, positive_beta_transform, transformCoeff_diagonal, transformed_product.
* atom_rshift: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_recurrence.
* atom_jshift: proof_shape: bind-only; escape_witness: none;
  consumers: diagonal_recurrence.
* diagonal_recurrence: proof_shape: bind-only; escape_witness: none;
  consumers: positive_beta_transform.
* scale_succ: proof_shape: bind-only; escape_witness: none;
  consumers: positive_beta_transform.
* gammaCoeff_zero: proof_shape: bind-only; escape_witness: none;
  consumers: positive_beta_transform.
* gammaCoeff_one: proof_shape: bind-only; escape_witness: none;
  consumers: positive_beta_transform.
* gammaCoeff_recurrence: proof_shape: bind-only; escape_witness: none;
  consumers: positive_beta_transform.
* positive_beta_transform: proof_shape: content; escape_witness: positive_beta_transform;
  consumers: series_identification.
* transformCoeff: proof_shape: bind-only (definition); escape_witness: none;
  consumers: gamma_half, series_identification, transformCoeff_diagonal, transformed_delta, transformed_product.
* series_identification: proof_shape: content; escape_witness: positive_beta_transform;
  consumers: gamma_half.
* transformCoeff_diagonal: proof_shape: bind-only; escape_witness: none;
  consumers: transformed_product.
* scale_neutral: proof_shape: bind-only; escape_witness: none;
  consumers: gamma_half.
* scale_pos: proof_shape: bind-only; escape_witness: none;
  consumers: gamma_half.
* diagonal_product: proof_shape: bind-only; escape_witness: none;
  consumers: transformed_product.
* atom_product: proof_shape: bind-only; escape_witness: none;
  consumers: transformed_product.
* transformed_product: proof_shape: bind-only; escape_witness: none;
  consumers: transformed_delta.
* transformed_delta: proof_shape: bind-only; escape_witness: none;
  consumers: gamma_half.
* gammaDelta: proof_shape: bind-only (definition); escape_witness: none;
  consumers: KarpZhangConjecture.Result.claim, KarpZhangConjecture.Result.result, gamma_half.
* gamma_half: proof_shape: content; escape_witness: positive_beta_transform;
  consumers: KarpZhangConjecture.Result.result.

Direct frozen D5 dependencies, with same-delivery helpers recursively inlined:
* F1: GID D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer;
  declaration statement_id:
  sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797.
Per-declaration live-path dependencies (F labels above; omitted declarations: none):
* KarpZhangGamma.Series.gamma_half: F1.
All KarpZhang dependencies are same-delivery declarations.
Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Analytic.KarpZhangGamma.Series

open Smoothing Result
open D5.S3.Analytic.KarpZhangReciprocal.Result (IsLogConcave)

/-- The literal coefficient in the gamma series, before multiplication by y. -/
def gammaCoeff (t : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (t + n) / (Real.Gamma (2 * t + n) * (n.factorial : ℝ))

/-- The positive factor in the beta transformation. The exponent is real. -/
def scale (t : ℝ) : ℝ := Real.sqrt Real.pi * (2 : ℝ) ^ (1 - 2 * t)

private def indices (n : ℕ) : Finset (ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1)).filter (fun p => p.1 + 2 * p.2 = n)

private theorem mem_indices (n : ℕ) (p : ℕ × ℕ) :
    p ∈ indices n ↔ p.1 + 2 * p.2 = n := by
  simp only [indices, mem_filter, mem_product, mem_range]
  omega

private def diagonal (f : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ indices n, f p.1 p.2

private theorem diagonal_eq (f : ℕ → ℕ → ℝ) (n : ℕ) :
    diagonal f n = ∑ j ∈ range (n / 2 + 1), f (n - 2 * j) j := by
  unfold diagonal
  apply sum_bij (fun p _ => p.2)
  · intro p hp
    rw [mem_indices] at hp
    simp only [mem_range]
    omega
  · intro p hp q hq h
    rw [mem_indices] at hp hq
    apply Prod.ext <;> omega
  · intro j hj
    have hj' := mem_range.mp hj
    refine ⟨(n - 2 * j, j), ?_, rfl⟩
    rw [mem_indices]
    change n - 2 * j + 2 * j = n
    omega
  · intro p hp
    rw [mem_indices] at hp
    change f p.1 p.2 = f (n - 2 * p.2) p.2
    rw [show n - 2 * p.2 = p.1 by omega]

private theorem diagonal_mul_left (c : ℝ) (f : ℕ → ℕ → ℝ) (n : ℕ) :
    diagonal (fun r j => c * f r j) n = c * diagonal f n := by
  simp only [diagonal, mul_sum]

private theorem diagonal_rshift (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ indices (n + 1), (p.1 : ℝ) * f p.1 p.2) =
      diagonal (fun r j => ((r + 1 : ℕ) : ℝ) * f (r + 1) j) n := by
  classical
  let s := (indices (n + 1)).filter (fun p => 0 < p.1)
  have hzero : (∑ p ∈ s, (p.1 : ℝ) * f p.1 p.2) =
      ∑ p ∈ indices (n + 1), (p.1 : ℝ) * f p.1 p.2 := by
    apply sum_subset (filter_subset _ _)
    intro p hp hnot
    have hp0 : p.1 = 0 := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hp, by omega⟩)
    simp [hp0]
  rw [← hzero]
  unfold diagonal
  apply sum_bij (fun p _ => (p.1 - 1, p.2))
  · intro p hp
    simp only [s, mem_filter, mem_indices] at hp
    rw [mem_indices]
    change p.1 - 1 + 2 * p.2 = n
    omega
  · intro p hp q hq heq
    simp only [s, mem_filter, mem_indices] at hp hq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  · intro p hp
    rw [mem_indices] at hp
    refine ⟨(p.1 + 1, p.2), ?_, ?_⟩
    · simp only [s, mem_filter, mem_indices]
      omega
    · apply Prod.ext <;> simp
  · intro p hp
    simp only [s, mem_filter, mem_indices] at hp
    change (p.1 : ℝ) * f p.1 p.2 =
      ((p.1 - 1 + 1 : ℕ) : ℝ) * f (p.1 - 1 + 1) p.2
    rw [show p.1 - 1 + 1 = p.1 by omega]

private theorem diagonal_jshift (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ indices (n + 2), (2 * p.2 : ℝ) * f p.1 p.2) =
      diagonal (fun r j => (2 * (j + 1) : ℝ) * f r (j + 1)) n := by
  classical
  let s := (indices (n + 2)).filter (fun p => 0 < p.2)
  have hzero : (∑ p ∈ s, (2 * p.2 : ℝ) * f p.1 p.2) =
      ∑ p ∈ indices (n + 2), (2 * p.2 : ℝ) * f p.1 p.2 := by
    apply sum_subset (filter_subset _ _)
    intro p hp hnot
    have hp0 : p.2 = 0 := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hp, by omega⟩)
    simp [hp0]
  rw [← hzero]
  unfold diagonal
  apply sum_bij (fun p _ => (p.1, p.2 - 1))
  · intro p hp
    simp only [s, mem_filter, mem_indices] at hp
    rw [mem_indices]
    change p.1 + 2 * (p.2 - 1) = n
    omega
  · intro p hp q hq heq
    simp only [s, mem_filter, mem_indices] at hp hq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  · intro p hp
    rw [mem_indices] at hp
    refine ⟨(p.1, p.2 + 1), ?_, ?_⟩
    · simp only [s, mem_filter, mem_indices]
      omega
    · apply Prod.ext <;> simp
  · intro p hp
    simp only [s, mem_filter, mem_indices] at hp
    have hs : p.2 - 1 + 1 = p.2 := by omega
    have hcast : ((p.2 - 1 : ℕ) : ℝ) + 1 = (p.2 : ℝ) := by
      exact_mod_cast hs
    change (2 * (p.2 : ℝ)) * f p.1 p.2 =
      (2 * (((p.2 - 1 : ℕ) : ℝ) + 1)) * f p.1 (p.2 - 1 + 1)
    rw [hs, hcast]

private def atom (a : ℝ) (r j : ℕ) : ℝ :=
  1 / ((r.factorial : ℝ) * (j.factorial : ℝ) * Real.Gamma (a + j) *
    (2 : ℝ) ^ r * (16 : ℝ) ^ j)

private theorem atom_rshift (a : ℝ) (r j : ℕ) :
    ((r + 1 : ℕ) : ℝ) * atom a (r + 1) j = (1 / 2 : ℝ) * atom a r j := by
  have hr : (r : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero r
  simp only [atom, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (((r : ℝ) + 1) * ((r : ℝ) + 1)⁻¹) *
        ((1 / 2 : ℝ) * ((r.factorial : ℝ)⁻¹ * (j.factorial : ℝ)⁻¹ *
          (Real.Gamma (a + j))⁻¹ * ((2 : ℝ) ^ r)⁻¹ * ((16 : ℝ) ^ j)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hr]; ring

private theorem atom_jshift (a : ℝ) (r j : ℕ) :
    (2 * (j + 1) : ℝ) * atom a r (j + 1) = (1 / 8 : ℝ) * atom (a + 1) r j := by
  have hj : (j : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero j
  have he : a + ((j + 1 : ℕ) : ℝ) = a + 1 + j := by push_cast; ring
  unfold atom
  rw [he]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (((j : ℝ) + 1) * ((j : ℝ) + 1)⁻¹) *
        ((1 / 8 : ℝ) * ((r.factorial : ℝ)⁻¹ * (j.factorial : ℝ)⁻¹ *
          (Real.Gamma (a + 1 + j))⁻¹ * ((2 : ℝ) ^ r)⁻¹ * ((16 : ℝ) ^ j)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hj]; ring

private theorem diagonal_recurrence (a : ℝ) (n : ℕ) :
    ((n + 2 : ℕ) : ℝ) * diagonal (atom a) (n + 2) =
      diagonal (atom a) (n + 1) / 2 + diagonal (atom (a + 1)) n / 8 := by
  have heuler : ((n + 2 : ℕ) : ℝ) * diagonal (atom a) (n + 2) =
      (∑ p ∈ indices (n + 2), (p.1 : ℝ) * atom a p.1 p.2) +
        ∑ p ∈ indices (n + 2), (2 * p.2 : ℝ) * atom a p.1 p.2 := by
    rw [diagonal, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have he : ((n + 2 : ℕ) : ℝ) = (p.1 : ℝ) + 2 * (p.2 : ℝ) := by
      exact_mod_cast ((mem_indices (n + 2) p).mp hp).symm
    rw [he]
    ring
  rw [heuler, diagonal_rshift (atom a) (n + 1), diagonal_jshift (atom a) n]
  simp only [atom_rshift, atom_jshift, diagonal_mul_left]
  ring

private theorem scale_succ (t : ℝ) : scale (t + 1) = scale t / 4 := by
  have he : 1 - 2 * t = (1 - 2 * (t + 1)) + 2 := by ring
  unfold scale
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num [Real.rpow_natCast]
  <;> ring

private theorem gammaCoeff_zero (t : ℝ) (ht : 0 < t) :
    gammaCoeff t 0 = scale t / Real.Gamma (t + 1 / 2) := by
  have h := Real.Gamma_mul_Gamma_add_half_of_pos ht
  have hg := ne_of_gt (Real.Gamma_pos_of_pos (show 0 < t + 1 / 2 by linarith))
  have hg2 := ne_of_gt (Real.Gamma_pos_of_pos (show 0 < 2 * t by linarith))
  simp only [gammaCoeff, Nat.cast_zero, add_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one, scale]
  apply (div_eq_div_iff hg2 hg).2
  calc
    _ = Real.Gamma (2 * t) * (2 : ℝ) ^ (1 - 2 * t) * Real.sqrt Real.pi := h
    _ = _ := by ring

private theorem gammaCoeff_one (t : ℝ) (ht : 0 < t) :
    gammaCoeff t 1 = gammaCoeff t 0 / 2 := by
  have hg2 := ne_of_gt (Real.Gamma_pos_of_pos (show 0 < 2 * t by linarith))
  simp only [gammaCoeff, Nat.cast_one, Nat.cast_zero, add_zero,
    Nat.factorial_zero, Nat.factorial_one, mul_one,
    Real.Gamma_add_one (ne_of_gt ht),
    Real.Gamma_add_one (show 2 * t ≠ 0 by positivity)]
  field_simp [ne_of_gt ht, hg2]
  <;> ring

private theorem gammaCoeff_recurrence (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ((n + 2 : ℕ) : ℝ) * gammaCoeff t (n + 2) =
      gammaCoeff t (n + 1) / 2 + gammaCoeff (t + 1) n / 2 := by
  have ht0 : 0 < t + n := by positivity
  have ht1 : 0 < t + n + 1 := by positivity
  have hd0 : 0 < 2 * t + n := by positivity
  have hd1 : 0 < 2 * t + n + 1 := by positivity
  have hgf := ne_of_gt (Real.Gamma_pos_of_pos hd0)
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have he1 : t + 1 + (n : ℝ) = t + n + 1 := add_right_comm t 1 (n : ℝ)
  have he2 : 2 * (t + 1) + (n : ℝ) = (2 * t + n + 1) + 1 := by ring
  have he3 : t + ((n + 2 : ℕ) : ℝ) = (t + n + 1) + 1 := by push_cast; ring
  have he4 : 2 * t + ((n + 2 : ℕ) : ℝ) = (2 * t + n + 1) + 1 := by push_cast; ring
  have he5 : t + ((n + 1 : ℕ) : ℝ) = t + n + 1 := by push_cast; ring
  have he6 : 2 * t + ((n + 1 : ℕ) : ℝ) = 2 * t + n + 1 := by push_cast; ring
  unfold gammaCoeff
  rw [he1, he2, he3, he4, he5, he6]
  simp only [
    Real.Gamma_add_one (ne_of_gt ht1), Real.Gamma_add_one (ne_of_gt hd1),
    Real.Gamma_add_one (ne_of_gt ht0), Real.Gamma_add_one (ne_of_gt hd0)]
  simp only [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hgf, hnf, ne_of_gt hd0, ne_of_gt hd1,
    show (n : ℝ) + 1 ≠ 0 by positivity, show (n : ℝ) + 1 + 1 ≠ 0 by positivity]
  <;> ring

/-- `positive_beta_transform`, proved by finite recurrence simultaneously for all positive t. -/
theorem positive_beta_transform (n : ℕ) : ∀ t : ℝ, 0 < t →
    gammaCoeff t n = scale t *
      ∑ j ∈ range (n / 2 + 1),
        1 / (((n - 2 * j).factorial : ℝ) * (j.factorial : ℝ) *
          Real.Gamma (t + 1 / 2 + j) * (2 : ℝ) ^ (n - 2 * j) * (16 : ℝ) ^ j) := by
  have hmain : ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      gammaCoeff t n = scale t * diagonal (atom (t + 1 / 2)) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht
      rcases n with _ | n
      · simpa [diagonal_eq, atom, div_eq_mul_inv] using gammaCoeff_zero t ht
      · rcases n with _ | n
        · rw [gammaCoeff_one t ht, gammaCoeff_zero t ht]
          simp [diagonal_eq, atom, div_eq_mul_inv, mul_inv_rev]
          <;> ring
        · have hrec := gammaCoeff_recurrence t ht n
          have hdiag := diagonal_recurrence (t + 1 / 2) n
          rw [ih (n + 1) (by omega) t ht,
            ih n (by omega) (t + 1) (by linarith), scale_succ] at hrec
          have ha : t + 1 + 1 / 2 = (t + 1 / 2) + 1 := add_right_comm t 1 (1 / 2)
          rw [ha] at hrec
          have hn : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := Nat.ofNat_pos'
          have hscaled := congrArg (fun z : ℝ => scale t * z) hdiag
          apply mul_left_cancel₀ (ne_of_gt hn)
          nlinarith only [hrec, hscaled]
  simpa only [diagonal_eq, atom] using hmain n

/-- Coefficient after substituting z=x/2 and w=x^2/16 in H(a;z,w). -/
def transformCoeff (y : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (n / 2 + 1),
    y n / (((n - 2 * j).factorial : ℝ) * (j.factorial : ℝ) *
      Real.Gamma (a + j) * (2 : ℝ) ^ (n - 2 * j) * (16 : ℝ) ^ j)

/-- The identification of the gamma series with the positive two-variable transform. -/
theorem series_identification (y : ℕ → ℝ) (t : ℝ) (ht : 0 < t) (n : ℕ) :
    y n * gammaCoeff t n = scale t * transformCoeff y (t + 1 / 2) n := by
  rw [positive_beta_transform n t ht]
  unfold transformCoeff
  simp only [div_eq_mul_inv, one_mul, ← mul_sum]
  ring

private theorem transformCoeff_diagonal (y : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    transformCoeff y a n = diagonal (fun r j => y (2 * j + r) * atom a r j) n := by
  rw [diagonal_eq]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  rw [show 2 * j + (n - 2 * j) = n by omega]
  simp only [atom, div_eq_mul_inv, one_mul]

private theorem scale_neutral (t α β : ℝ) :
    scale (t + α) * scale (t + β) = scale t * scale (t + α + β) := by
  have he : (1 - 2 * (t + α)) + (1 - 2 * (t + β)) =
      (1 - 2 * t) + (1 - 2 * (t + α + β)) := by ring
  unfold scale
  calc
    _ = (Real.sqrt Real.pi) ^ 2 *
        ((2 : ℝ) ^ (1 - 2 * (t + α)) * (2 : ℝ) ^ (1 - 2 * (t + β))) := by ring
    _ = (Real.sqrt Real.pi) ^ 2 *
        ((2 : ℝ) ^ (1 - 2 * t) * (2 : ℝ) ^ (1 - 2 * (t + α + β))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), he,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by ring

private theorem scale_pos (t : ℝ) : 0 < scale t := by
  exact mul_pos (Real.sqrt_pos.2 Real.pi_pos)
    (Real.rpow_pos_of_pos (by norm_num) _)

private theorem diagonal_product (f g : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1), diagonal f k * diagonal g (n - k)) =
      ∑ m ∈ range (n / 2 + 1), ∑ i ∈ range (m + 1),
        ∑ r ∈ range (n - 2 * m + 1), f r i * g (n - 2 * m - r) (m - i) := by
  classical
  simp only [diagonal_eq, sum_mul, mul_sum]
  simp only [← sum_product', sum_sigma']
  apply sum_bij (fun p _ =>
    (⟨p.2.2 + p.2.1, (p.2.2, p.1 - 2 * p.2.2)⟩ : Σ _ : ℕ, ℕ × ℕ))
  · rintro ⟨k, j, i⟩ hp
    simp only [mem_sigma, mem_product, mem_range] at hp ⊢
    omega
  · rintro ⟨k, j, i⟩ hp ⟨l, v, u⟩ hq heq
    simp only [mem_sigma, mem_product, mem_range] at hp hq
    have h1 : i + j = u + v := congrArg Sigma.fst heq
    have h2 : (i, k - 2 * i) = (u, l - 2 * u) :=
      congrArg (fun p : Σ _ : ℕ, ℕ × ℕ => p.2) heq
    have hi : i = u := congrArg Prod.fst h2
    have hdiff : k - 2 * i = l - 2 * u := congrArg Prod.snd h2
    have hk : k = l := by omega
    have hj : j = v := by omega
    subst l; subst u; subst v
    rfl
  · rintro ⟨m, i, r⟩ hp
    simp only [mem_sigma, mem_product, mem_range] at hp
    refine ⟨⟨r + 2 * i, (m - i, i)⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_product, mem_range]
      omega
    · have hm : i + (m - i) = m := by omega
      change (⟨i + (m - i), (i, r + 2 * i - 2 * i)⟩ : Σ _ : ℕ, ℕ × ℕ) =
        ⟨m, (i, r)⟩
      rw [hm, show r + 2 * i - 2 * i = r by omega]
  · rintro ⟨k, j, i⟩ hp
    simp only [mem_sigma, mem_product, mem_range] at hp
    change f (k - 2 * i) i * g (n - k - 2 * j) j =
      f (k - 2 * i) i * g (n - 2 * (i + j) - (k - 2 * i)) (i + j - i)
    rw [show i + j - i = j by omega,
      show n - 2 * (i + j) - (k - 2 * i) = n - k - 2 * j by omega]

private theorem atom_product (a b : ℝ) (N m r k : ℕ) (hr : r ≤ N) (hk : k ≤ m) :
    atom a r k * atom b (N - r) (m - k) =
      (1 / ((2 : ℝ) ^ N * (16 : ℝ) ^ m)) *
        (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
          Real.Gamma (a + k) * Real.Gamma (b + (m - k)))) *
        (1 / ((r.factorial : ℝ) * ((N - r).factorial : ℝ))) := by
  have h2 : (2 : ℝ) ^ r * (2 : ℝ) ^ (N - r) = (2 : ℝ) ^ N := pow_mul_pow_sub (2 : ℝ) hr
  have h16 : (16 : ℝ) ^ k * (16 : ℝ) ^ (m - k) = (16 : ℝ) ^ m := pow_mul_pow_sub (16 : ℝ) hk
  calc
    _ = (1 / (((2 : ℝ) ^ r * (2 : ℝ) ^ (N - r)) *
          ((16 : ℝ) ^ k * (16 : ℝ) ^ (m - k)))) *
        (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
          Real.Gamma (a + k) * Real.Gamma (b + (m - k)))) *
        (1 / ((r.factorial : ℝ) * ((N - r).factorial : ℝ))) := by
      simp only [atom, div_eq_mul_inv, mul_inv_rev, one_mul]
      rw [Nat.cast_sub hk]
      ring
    _ = _ := by rw [h2, h16]

private theorem transformed_product (y : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1), transformCoeff y a k * transformCoeff y b (n - k)) =
      ∑ m ∈ range (n / 2 + 1),
        (1 / ((2 : ℝ) ^ (n - 2 * m) * (16 : ℝ) ^ m)) *
          ∑ k ∈ range (m + 1),
            (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
              Real.Gamma (a + k) * Real.Gamma (b + (m - k)))) *
              productCoeff (fun r => y (2 * k + r))
                (fun r => y (2 * (m - k) + r)) (n - 2 * m) := by
  simp only [transformCoeff_diagonal]
  rw [diagonal_product]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [productCoeff, mul_sum, mul_sum]
  apply sum_congr rfl
  intro r hr
  have h := atom_product a b (n - 2 * m) m r k
    (by have := mem_range.mp hr; omega) (by have := mem_range.mp hk; omega)
  calc
    _ = (y (2 * k + r) * y (2 * (m - k) + (n - 2 * m - r))) *
        (atom a r k * atom b (n - 2 * m - r) (m - k)) := by ring
    _ = _ := by rw [h]; simp only [div_eq_mul_inv, one_mul]; ring

private theorem transformed_delta (y : ℕ → ℝ) (a α β : ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      (transformCoeff y (a + α) k * transformCoeff y (a + β) (n - k) -
        transformCoeff y a k * transformCoeff y (a + α + β) (n - k))) =
      ∑ m ∈ range (n / 2 + 1),
        (1 / ((2 : ℝ) ^ (n - 2 * m) * (16 : ℝ) ^ m)) *
          transformDelta y a α β (n - 2 * m) m := by
  rw [sum_sub_distrib, transformed_product, transformed_product, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  unfold transformDelta
  apply sum_congr rfl
  intro k hk
  simp only [Kernel.kernel, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The literal degree-n finite Cauchy coefficient of the gamma-series Turanian. -/
def gammaDelta (y : ℕ → ℝ) (μ α β : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (y k * gammaCoeff (μ + α) k * (y (n - k) * gammaCoeff (μ + β) (n - k)) -
      y k * gammaCoeff μ k * (y (n - k) * gammaCoeff (μ + α + β) (n - k)))

/-- `gamma_half`: every coefficient is nonnegative, for all real nonnegative shifts. -/
theorem gamma_half (y : ℕ → ℝ) (hy : IsLogConcave y)
    (μ α β : ℝ) (hμ : 0 < μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    0 ≤ gammaDelta y μ α β n := by
  have hscale := scale_neutral μ α β
  have hid : gammaDelta y μ α β n = (scale μ * scale (μ + α + β)) *
      ∑ m ∈ range (n / 2 + 1),
        (1 / ((2 : ℝ) ^ (n - 2 * m) * (16 : ℝ) ^ m)) *
          transformDelta y (μ + 1 / 2) α β (n - 2 * m) m := by
    calc
      _ = (scale μ * scale (μ + α + β)) *
          ∑ k ∈ range (n + 1),
            (transformCoeff y (μ + 1 / 2 + α) k *
                transformCoeff y (μ + 1 / 2 + β) (n - k) -
              transformCoeff y (μ + 1 / 2) k *
                transformCoeff y (μ + 1 / 2 + α + β) (n - k)) := by
        unfold gammaDelta
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        rw [series_identification y (μ + α) (by linarith),
          series_identification y (μ + β) (by linarith),
          series_identification y μ hμ,
          series_identification y (μ + α + β) (by linarith)]
        rw [show μ + α + 1 / 2 = μ + 1 / 2 + α by ring,
          show μ + β + 1 / 2 = μ + 1 / 2 + β by ring,
          show μ + α + β + 1 / 2 = μ + 1 / 2 + α + β by ring]
        calc
          _ = (scale (μ + α) * scale (μ + β)) *
                (transformCoeff y (μ + 1 / 2 + α) k *
                  transformCoeff y (μ + 1 / 2 + β) (n - k)) -
              (scale μ * scale (μ + α + β)) *
                (transformCoeff y (μ + 1 / 2) k *
                  transformCoeff y (μ + 1 / 2 + α + β) (n - k)) := by ring
          _ = _ := by rw [hscale]; ring
      _ = _ := by rw [transformed_delta]
  rw [hid]
  apply mul_nonneg (le_of_lt (mul_pos (scale_pos μ) (scale_pos (μ + α + β))))
  apply sum_nonneg
  intro m hm
  exact mul_nonneg (by positivity)
    (two_variable_nonneg y hy (μ + 1 / 2) α β (by linarith) hα hβ (n - 2 * m) m)

end D5.S3.Analytic.KarpZhangGamma.Series
