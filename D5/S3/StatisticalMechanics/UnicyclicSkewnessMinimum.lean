/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessMinimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The least unidirectional unicyclic current skewness is attained by one slow rate. -/

import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import D5.S3.Quantum.Transport.StrongAbsorption.Foundations

/-!
The normalized inverse rates lie in the standard simplex. Write `a` for its largest
coordinate and `b = (1-a)/(n-1)` for the mean of the remaining coordinates.
The nonnegative sums of `(x-b)^2` and `(a-x)*(x-b)^2` bound the second and third
moments. Completing squares then gives the sharp bound for `3p₂²-2p₃`.
The rates `(1/(n-1), 1, …, 1)` attain the bound.
-/

noncomputable section

open scoped BigOperators
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum

/-- The third scaled current cumulant divided by the first scaled current cumulant. -/
def skewness {n : ℕ} (k : Fin n → ℝ) : ℝ :=
  3 * powerSum n 2 (fun i => (k i)⁻¹) ^ 2 /
      powerSum n 1 (fun i => (k i)⁻¹) ^ 4 -
    2 * powerSum n 3 (fun i => (k i)⁻¹) /
      powerSum n 1 (fun i => (k i)⁻¹) ^ 3

/-- The conjectured finite-state minimum. -/
def minimumValue (n : ℕ) : ℝ :=
  -(8 - 8 * (n : ℝ) + (n : ℝ) ^ 2) / (16 * ((n : ℝ) - 1) ^ 2)

/-- All positive clockwise rate vectors on every cycle with at least two states. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    IsLeast {s : ℝ | ∃ k : Fin n → ℝ, (∀ i, 0 < k i) ∧ s = skewness k}
      (minimumValue n)

private def simplexFunctional {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  3 * powerSum n 2 x ^ 2 - 2 * powerSum n 3 x

private lemma normalized_simplex {n : ℕ} (hn : 0 < n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) :
    (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ∈ stdSimplex ℝ (Fin n) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have he : (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) =
      (∑ i, (k i)⁻¹)⁻¹ • (fun i => (k i)⁻¹) := by
    funext i
    delta powerSum
    simp [div_eq_mul_inv, mul_comm]
  rw [he]
  exact Matrix.CollatzWielandt.inv_sum_smul_mem_stdSimplex_of_nonneg_ne_zero
    (fun i => le_of_lt (inv_pos.mpr (hk i)))
    (Pi.ne_zero_of_pos fun i => inv_pos.mpr (hk i))

private lemma skewness_normalized {n : ℕ} (k : Fin n → ℝ) :
    skewness k = simplexFunctional
      (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) := by
  delta skewness simplexFunctional powerSum
  simp only [div_pow, ← Finset.sum_div]
  ring

private lemma algebra_lower_bound (r a b p q : ℝ) (hr : 1 ≤ r)
    (hab : a + r * b = 1) (hba : b ≤ a) (ha : 0 ≤ a)
    (hp : a ^ 2 + r * b ^ 2 ≤ p)
    (hq : q ≤ (a + 2 * b) * p - 2 * a * b - b ^ 2 + (r + 1) * a * b ^ 2) :
    -(r ^ 2 - 6 * r + 1) / (16 * r ^ 2) ≤ 3 * p ^ 2 - 2 * q := by
  have hrp : 0 < r := by linarith
  have hrn : r ≠ 0 := ne_of_gt hrp
  have hb : b = (1 - a) / r := by
    apply (eq_div_iff hrn).mpr
    linarith
  let d := p - (a ^ 2 + r * b ^ 2)
  let h := 3 * (a ^ 2 + r * b ^ 2) ^ 2 - 2 * (a ^ 3 + r * b ^ 3)
  let g := -(r ^ 2 - 6 * r + 1) / (16 * r ^ 2)
  have hd : 0 ≤ d := sub_nonneg.mpr hp
  have hz : 0 ≤ (r + 1) * a - 1 := by nlinarith
  have hdiff : h - g = (2 * a - 1) ^ 2 *
      (12 * ((r + 1) * a - 1) ^ 2 + 4 * (r - 1) * ((r + 1) * a - 1) +
        (r - 1) ^ 2) / (16 * r ^ 2) := by
    dsimp [h, g]
    rw [hb]
    field_simp
    ring
  have hh : g ≤ h := by
    have : 0 ≤ h - g := by
      rw [hdiff]
      positivity
    linarith
  have he : 3 * p ^ 2 - 2 * q ≥
      h + 3 * d ^ 2 + 2 * (a - b) * (3 * a - 1) * d := by
    have hi : 3 * p ^ 2 - 2 * ((a + 2 * b) * p - 2 * a * b - b ^ 2 +
        (r + 1) * a * b ^ 2) =
        h + 3 * d ^ 2 + 2 * (a - b) * (3 * a - 1) * d := by
      dsimp [h, d]
      rw [hb]
      field_simp
      ring
    linarith
  by_cases hc : 0 ≤ 3 * a - 1
  · have hepos := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sub_nonneg.mpr hba)) hc) hd
    nlinarith only [he, hh, hepos, sq_nonneg d]
  · have hr2 : 2 ≤ r := by
      nlinarith [mul_nonneg (le_of_lt hrp) (show 0 ≤ 1 - 3 * a by linarith)]
    let u := 18 * (r + 1) * a ^ 2 + 3 * (r ^ 2 - 2 * r - 12) * a + r ^ 2 - 8 * r + 18
    have hu : 0 ≤ u := by
      by_cases hr8 : r ≤ 8
      · have hid : 72 * (r + 1) * u =
            (36 * (r + 1) * a + 3 * (r ^ 2 - 2 * r - 12)) ^ 2 +
              9 * r * (8 - r) * (r - 2) ^ 2 := by dsimp [u]; ring
        have hv : 0 ≤ 9 * r * (8 - r) * (r - 2) ^ 2 := by positivity
        nlinarith [sq_nonneg (36 * (r + 1) * a + 3 * (r ^ 2 - 2 * r - 12))]
      · have hv : 0 ≤ r ^ 2 - 2 * r - 12 := by nlinarith
        have hw : 0 ≤ r ^ 2 - 8 * r + 18 := by nlinarith [sq_nonneg (r - 4)]
        have hv1 : 0 ≤ 18 * (r + 1) * a ^ 2 := by positivity
        have hv2 : 0 ≤ 3 * (r ^ 2 - 2 * r - 12) * a := by positivity
        dsimp [u]
        linarith only [hv1, hv2, hw]
    have hk : h - (a - b) ^ 2 * (3 * a - 1) ^ 2 / 3 - g =
        (1 / 3 - a) * u / (9 * r ^ 2) +
          (11 * (r - 2) ^ 2 + 10 * (r - 2) + 3) / (432 * r ^ 2) := by
      dsimp [h, g, u]
      rw [hb]
      field_simp
      ring
    have hkpos : 0 ≤ h - (a - b) ^ 2 * (3 * a - 1) ^ 2 / 3 - g := by
      rw [hk]
      have hac : 0 ≤ 1 / 3 - a := by linarith
      positivity
    have hid : h + 3 * d ^ 2 + 2 * (a - b) * (3 * a - 1) * d - g =
        (h - (a - b) ^ 2 * (3 * a - 1) ^ 2 / 3 - g) +
          (3 * d + (a - b) * (3 * a - 1)) ^ 2 / 3 := by ring
    have hpos : 0 ≤ h + 3 * d ^ 2 + 2 * (a - b) * (3 * a - 1) * d - g := by
      rw [hid]
      exact add_nonneg hkpos (div_nonneg (sq_nonneg _) (by norm_num))
    linarith only [he, hpos]

private lemma simplex_lower_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) : minimumValue n ≤ simplexFunctional x := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ x hne
  let a := x i
  let r := (n : ℝ) - 1
  let b := (1 - a) / r
  let p := ∑ j, x j ^ 2
  let q := ∑ j, x j ^ 3
  have hr : 1 ≤ r := by
    dsimp [r]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hrp : 0 < r := by linarith
  have hab : a + r * b = 1 := by dsimp [b]; field_simp [ne_of_gt hrp]; ring
  have ha : 0 ≤ a := hx.1 i
  have hna : 1 ≤ (n : ℝ) * a := by
    calc
      1 = ∑ j, x j := hx.2.symm
      _ ≤ ∑ _ : Fin n, a := Finset.sum_le_sum fun j _ => hmax j (Finset.mem_univ j)
      _ = (n : ℝ) * a := by simp
  have hba : b ≤ a := by
    apply (div_le_iff₀ hrp).mpr
    dsimp [r] at *
    linarith
  have hs : ∑ j, (x j - b) ^ 2 = p - 2 * b + (n : ℝ) * b ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hx.2, mul_one, p]
  have hp : a ^ 2 + r * b ^ 2 ≤ p := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      sq_nonneg (x j - b)) (Finset.mem_univ i)
    rw [hs] at hi
    change (a - b) ^ 2 ≤ _ at hi
    dsimp [r] at *
    have hbb := congrArg (fun z : ℝ => z * b) hab
    nlinarith only [hi, hbb]
  have hsum : 0 ≤ ∑ j, (a - x j) * (x j - b) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sub_nonneg.mpr (hmax j (Finset.mem_univ j)))
      (sq_nonneg _)
  have he : ∑ j, (a - x j) * (x j - b) ^ 2 =
      -q + (a + 2 * b) * p - (2 * a * b + b ^ 2) + (n : ℝ) * a * b ^ 2 := by
    calc
      _ = ∑ j, (-(x j ^ 3) + (a + 2 * b) * x j ^ 2 -
          (2 * a * b + b ^ 2) * x j + a * b ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hx.2, mul_one, p, q]
        ring
  have hq : q ≤ (a + 2 * b) * p - 2 * a * b - b ^ 2 + (r + 1) * a * b ^ 2 := by
    rw [he] at hsum
    dsimp [r]
    nlinarith
  have hbound := algebra_lower_bound r a b p q hr hab hba ha hp hq
  change minimumValue n ≤ 3 * p ^ 2 - 2 * q
  convert hbound using 1
  dsimp [minimumValue, r]
  congr 1 <;> ring

private lemma attaining_rates (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : Fin n → ℝ, (∀ i, 0 < k i) ∧ minimumValue n = skewness k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  refine ⟨fun i => if i = 0 then (m : ℝ)⁻¹ else 1, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs <;> positivity
  · have hs (j : ℕ) :
        powerSum (m + 1) j (fun i : Fin (m + 1) =>
          (if i = 0 then (m : ℝ)⁻¹ else 1)⁻¹) =
          (m : ℝ) ^ j + m := by
      delta powerSum
      simp [Fin.sum_univ_succ]
    delta skewness minimumValue
    simp only [hs, Nat.cast_succ, add_sub_cancel_right]
    field_simp (disch := positivity)
    ring

/-- The conjectured skewness minimum holds for every positive rate vector and is attained. -/
theorem result : claim := by
  intro n hn
  refine ⟨attaining_rates n hn, ?_⟩
  rintro s ⟨k, hk, rfl⟩
  rw [skewness_normalized]
  exact simplex_lower_bound hn _ (normalized_simplex (by omega) k hk)

end D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
