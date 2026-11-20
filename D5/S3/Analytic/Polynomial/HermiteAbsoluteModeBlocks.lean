/- GID: D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: none
   digest: Absolute Hermite mode: threshold, floor formula, blocks, ties and interlacing with the signed mode. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The absolute Hermite mode: quadratic threshold, floor formula, growth, block structure of its
differences, the structure of ties, the equality of signed and absolute maxima, and interlacing
with the signed mode.

admission_basis: escape-witness. proof_shape: content for signed_eq, even_le, interlace,
B_eq_iff, tie_structure, b_window, h_L, three_iff and result; threshold_iff, unique_or_two and
unique_iff are consumed helpers recombining frozen lemmas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Polynomial.HermiteAbsoluteModeBlocks

open D5.S3.Analytic.Polynomial
open D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
open D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders

private theorem signed_eq (n r : ℕ) (hr : 2 * r ≤ n) :
    HermiteSignedMode.signedCoeff n (n - 2 * r) = (-1) ^ r * weight n r := by
  have hval : HermiteSignedMode.signedCoeff n (n - 2 * r) =
      (-1) ^ r * ((n.factorial : ℚ) * 2 ^ (n - 2 * r) / (r.factorial * (n - 2 * r).factorial)) := by
    have h : n - 2 * r ≤ n ∧ (n - (n - 2 * r)) % 2 = 0 := by constructor <;> omega
    have hs : n - (n - 2 * r) = 2 * r := by omega
    rw [HermiteSignedMode.signedCoeff, if_pos h, hs, show 2 * r / 2 = r by omega]
    ring
  have hP : (0 : ℚ) ≤ (n.factorial : ℚ) * 2 ^ (n - 2 * r) / (r.factorial * (n - 2 * r).factorial) := by
    positivity
  unfold weight
  rw [hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hP]

private theorem decreasing_after (n r : ℕ) (hr : mode n < r + 1) (h2 : 2 * (r + 1) ≤ n) :
    weight n (r + 1) < weight n r := by
  have hnot : ¬ rises n (r + 1) := fun h => by have := le_mode h; omega
  have hlt : second (n - 2 * (r + 1)) < 4 * (r + 1) := by
    by_contra h; push Not at h; exact hnot ⟨h2, h⟩
  have he := adjacent n r h2
  have hw := weight_pos n r (by omega)
  have hq : (second (n - 2 * (r + 1)) : ℚ) < 4 * (r + 1) := by exact_mod_cast hlt
  have hd : (0 : ℚ) < 4 * (r + 1) := by positivity
  nlinarith

private theorem even_le (n p : ℕ) (hp : 4 * p ≤ n) :
    weight n (2 * p) ≤ weight n (2 * HermiteSignedMode.mode n) := by
  have hq := (HermiteSignedMode.mode_rises n).1
  have hmax := (HermiteSignedMode.result.1 n).2.1 (n - 4 * p) (Nat.sub_le _ _)
  rw [HermiteSignedMode.polynomial_coeff n (n - 4 * p) (Nat.sub_le _ _),
    HermiteSignedMode.polynomial_coeff n (HermiteSignedMode.a n) (Nat.sub_le _ _)] at hmax
  have e1 := signed_eq n (2 * p) (by omega)
  have e2 := signed_eq n (2 * HermiteSignedMode.mode n) (by omega)
  rw [show n - 2 * (2 * p) = n - 4 * p by omega, pow_mul] at e1
  rw [show n - 2 * (2 * HermiteSignedMode.mode n) = HermiteSignedMode.a n by
    unfold HermiteSignedMode.a; omega, pow_mul] at e2
  simp only [neg_one_sq, one_pow, one_mul] at e1 e2
  rw [e1, e2] at hmax
  exact hmax

private theorem interlace (n : ℕ) :
    mode n ≤ 2 * HermiteSignedMode.mode n + 1 ∧ 2 * HermiteSignedMode.mode n ≤ mode n + 1 := by
  set q := HermiteSignedMode.mode n
  set t := mode n
  have hq := (HermiteSignedMode.mode_rises n).1
  have ht := (mode_rises n).1
  constructor
  · by_contra h
    push Not at h
    have h1 := strict_before n (2 * q) (by omega)
    have h2 : weight n (2 * q + 1) ≤ weight n (2 * (q + 1)) := by
      rcases Nat.lt_or_ge (2 * q + 2) t with hlt | hge
      · exact (strict_before n (2 * q + 1) (by omega)).le
      · have : 2 * (q + 1) = t := by omega
        rw [this]; exact weight_le_mode n _ (by omega)
    have := even_le n (q + 1) (by omega)
    linarith
  · by_contra h
    push Not at h
    obtain ⟨p, hp⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have h1 := decreasing_after n (2 * q - 1) (by omega) (by omega)
    have h2 := decreasing_after n (2 * q - 2) (by omega) (by omega)
    rw [show 2 * q - 1 + 1 = 2 * q by omega] at h1
    rw [show 2 * q - 2 + 1 = 2 * q - 1 by omega] at h2
    have := even_le n p (by omega)
    rw [show 2 * p = 2 * q - 2 by omega] at this
    linarith

private theorem B_le (n : ℕ) : weight n (2 * HermiteSignedMode.mode n) ≤ weight n (mode n) :=
  weight_le_mode n _ (by have := (HermiteSignedMode.mode_rises n).1; omega)

private theorem B_eq_iff (n : ℕ) :
    weight n (2 * HermiteSignedMode.mode n) = weight n (mode n) ↔
      HasExactlyTwo n ∨ Even (mode n) := by
  set q := HermiteSignedMode.mode n
  set t := mode n
  have hq := (HermiteSignedMode.mode_rises n).1
  have ht := (mode_rises n).1
  constructor
  · intro he
    rcases Nat.even_or_odd t with hev | hodd
    · exact Or.inr hev
    · left
      rcases equal_mode_indices n (2 * q) (by omega) he with h | h
      · exfalso
        have h' : 2 * q = t := h
        rw [← h'] at hodd
        exact (Nat.not_odd_iff_even.2 (even_two_mul q)) hodd
      · have heq : weight n (2 * q) = weight n (2 * q + 1) := by rw [h]; exact he
        have hs := (adjacent_equal n (2 * q) (by omega)).1 heq
        exact (tie_characterization n).2 ⟨2 * q + 1, by omega, by omega, hs⟩
  · rintro (hT | ⟨p, hp⟩)
    · obtain ⟨r, hr1, hr2, hs⟩ := (tie_characterization n).1 hT
      have hrt := tie_is_mode n r hr2 hs
      have heq : weight n (r - 1) = weight n r := by
        have hh : r - 1 + 1 = r := by omega
        have := (adjacent_equal n (r - 1) (by omega)).2 (by rw [hh]; exact hs)
        rwa [hh] at this
      rcases Nat.even_or_odd r with ⟨p, hp⟩ | ⟨p, hp⟩
      · have := even_le n p (by omega)
        rw [show 2 * p = r by omega, hrt] at this
        exact le_antisymm (B_le n) this
      · have := even_le n p (by omega)
        rw [show 2 * p = r - 1 by omega, heq, hrt] at this
        exact le_antisymm (B_le n) this
    · have := even_le n p (by omega)
      rw [show 2 * p = t by omega] at this
      exact le_antisymm (B_le n) this

private theorem tie_structure (n : ℕ) (hT : HasExactlyTwo n) :
    (∀ j, IsAbsMax n j ↔ j = b n ∨ j = b n + 2) ∧
      (HermiteSignedMode.physicistsHermite n).coeff (b n) *
        (HermiteSignedMode.physicistsHermite n).coeff (b n + 2) < 0 := by
  obtain ⟨r, hr1, hr2, hs⟩ := (tie_characterization n).1 hT
  have hrt := tie_is_mode n r hr2 hs
  have heq : weight n (r - 1) = weight n r := by
    have hh : r - 1 + 1 = r := by omega
    have := (adjacent_equal n (r - 1) (by omega)).2 (by rw [hh]; exact hs)
    rwa [hh] at this
  have hb : b n = n - 2 * r := by unfold b; rw [hrt]
  have hb2 : b n + 2 = n - 2 * (r - 1) := by rw [hb]; omega
  constructor
  · intro j
    rw [max_iff_weight]
    constructor
    · rintro ⟨s, hs2, rfl, hes⟩
      rcases equal_mode_indices n s hs2 hes with h | h
      · left; rw [hb, h, hrt]
      · right; rw [hb2]; congr 1; omega
    · rintro (rfl | rfl)
      · exact ⟨r, hr2, hb, by rw [hrt]⟩
      · exact ⟨r - 1, by omega, hb2, by rw [heq, hrt]⟩
  · rw [hb2, hb, HermiteSignedMode.polynomial_coeff n _ (Nat.sub_le _ _),
      HermiteSignedMode.polynomial_coeff n _ (Nat.sub_le _ _), signed_eq n r hr2,
      signed_eq n (r - 1) (by omega), heq]
    have hw := weight_pos n r hr2
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    have h1 : ((-1 : ℚ) ^ s) * (-1) ^ s = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have key : (-1 : ℚ) ^ s * -1 * weight n (s + 1) * ((-1) ^ s * weight n (s + 1)) =
        -(((-1) ^ s * (-1) ^ s) * (weight n (s + 1) * weight n (s + 1))) := by ring
    rw [key, h1, one_mul, neg_lt_zero]
    positivity


private theorem rises_iff (n r : ℕ) : rises n r ↔ 2 * r ≤ n ∧ 2 * n ≤ (n - 2 * r) ^ 2 + 5 * (n - 2 * r) + 2 := by
  unfold rises second
  constructor
  · rintro ⟨h2, h4⟩
    refine ⟨h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 2 * r = j := ⟨_, rfl⟩
    rw [hj] at h4 ⊢
    have : n = j + 2 * r := by omega
    subst this; nlinarith
  · rintro ⟨h2, hF⟩
    refine ⟨h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 2 * r = j := ⟨_, rfl⟩
    rw [hj] at hF ⊢
    have : n = j + 2 * r := by omega
    subst this; nlinarith

private theorem threshold_iff (n j : ℕ) (hj : j % 2 = n % 2) :
    b n ≤ j ↔ 2 * n ≤ j ^ 2 + 5 * j + 2 := by
  have hm := mode_rises n
  have hm2 := hm.1
  unfold b
  rcases Nat.lt_or_ge n j with hnj | hjn
  · constructor
    · intro _; nlinarith
    · intro _; omega
  obtain ⟨r, hr⟩ : ∃ r, n - j = 2 * r := ⟨(n - j) / 2, by omega⟩
  have hjr : j = n - 2 * r := by omega
  constructor
  · intro h
    have hle : r ≤ mode n := by omega
    have := ((rises_iff n r).1 (rises_lower hm hle)).2
    rw [← hjr] at this; exact this
  · intro h
    have := le_mode ((rises_iff n r).2 ⟨by omega, by rw [← hjr]; exact h⟩)
    omega

private theorem unique_or_two (k : ℕ) : (∃! j, IsAbsMax k j) ∨ HasExactlyTwo k := by
  by_cases hT : HasExactlyTwo k
  · exact Or.inr hT
  left
  have hm := (mode_rises k).1
  refine ⟨k - 2 * mode k, (max_iff_weight k _).2 ⟨mode k, hm, rfl, rfl⟩, fun j hj => ?_⟩
  obtain ⟨r, hr, rfl, he⟩ := (max_iff_weight k j).1 hj
  rcases equal_mode_indices k r hr he with h | h
  · rw [h]
  · exfalso
    apply hT
    have heq : weight k r = weight k (r + 1) := by rw [h]; exact he
    have ht := (adjacent_equal k r (by omega)).1 heq
    exact (tie_characterization k).2 ⟨r + 1, by omega, by omega, ht⟩

private theorem b_window (n : ℕ) : (√(8 * n + 17) - 5) / 2 ≤ b n ∧ (b n : ℝ) < (√(8 * n + 17) - 5) / 2 + 2 := by
  have hm := (mode_rises n).1
  have hpar : b n % 2 = n % 2 := by unfold b; omega
  have hF := (threshold_iff n (b n) hpar).1 le_rfl
  have hbn : b n ≤ n := Nat.sub_le _ _
  set s := √(8 * (n : ℝ) + 17) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 8 * n + 17 := Real.sq_sqrt (by positivity)
  constructor
  · have hFr : (2 * n : ℝ) ≤ b n ^ 2 + 5 * b n + 2 := by exact_mod_cast hF
    have : s ≤ 2 * b n + 5 := by by_contra h; push Not at h; nlinarith
    linarith
  · have : 2 * (b n : ℝ) + 1 < s := by
      rcases Nat.lt_or_ge (b n) 2 with h2 | h2
      · have hr : (b n : ℝ) ≤ 1 := by exact_mod_cast (show b n ≤ 1 by omega)
        have h0 : (0 : ℝ) ≤ b n := by positivity
        have hn0 : (0 : ℝ) ≤ n := by positivity
        by_contra h; push Not at h; nlinarith
      · have hnot : ¬ 2 * n ≤ (b n - 2) ^ 2 + 5 * (b n - 2) + 2 := fun h => by
          have := (threshold_iff n (b n - 2) (by omega)).2 h; omega
        push Not at hnot
        obtain ⟨i, hi⟩ : ∃ i, b n = i + 2 := ⟨b n - 2, by omega⟩
        rw [hi, Nat.add_sub_cancel] at hnot
        have hr : ((i : ℝ) ^ 2 + 5 * i + 2) < 2 * n := by exact_mod_cast hnot
        have hbi : (b n : ℝ) = i + 2 := by exact_mod_cast hi
        by_contra h; push Not at h; nlinarith
    linarith

private theorem t_floor (n : ℕ) : ⌊((2 * n + 5 : ℝ) - √(8 * n + 17)) / 4⌋ = (mode n : ℤ) := by
  obtain ⟨hl, hu⟩ := b_window n
  have hm := (mode_rises n).1
  have hb : (b n : ℝ) = n - 2 * mode n := by unfold b; push_cast [hm]; ring
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

private theorem b_growth (n : ℕ) : -(5 / 2 : ℝ) < (b n : ℝ) - √(2 * n) ∧ (b n : ℝ) - √(2 * n) < 2 := by
  obtain ⟨hl, hu⟩ := b_window n
  set s := √(8 * (n : ℝ) + 17)
  set t := √(2 * (n : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 8 * n + 17 := Real.sq_sqrt (by positivity)
  have htq : t ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have hlow : 2 * t < s := by by_contra h; push Not at h; nlinarith
  have hup : s ≤ 2 * t + 5 := by by_contra h; push Not at h; nlinarith
  constructor <;> linarith

private theorem exists_h (k : ℕ) : ∃ j, 4 * k ≤ second j := ⟨4 * k, by unfold second; nlinarith⟩

/-- `h_k = min {j : (j + 1)(j + 2) ≥ 4k}`. -/
noncomputable def hOffset (k : ℕ) : ℕ := Nat.find (exists_h k)

/-- `m_k = 2k + h_k`, the first degree with `t(n) ≥ k`. -/
noncomputable def absStart (k : ℕ) : ℕ := 2 * k + hOffset k

private theorem h_le_iff (k j : ℕ) : hOffset k ≤ j ↔ 4 * k ≤ second j :=
  ⟨fun h => (Nat.find_spec (exists_h k)).trans (second_mono h), fun h => Nat.find_min' _ h⟩

private theorem le_t_iff (n k : ℕ) : k ≤ mode n ↔ absStart k ≤ n := by
  constructor
  · intro h
    have hr := rises_lower (mode_rises n) h
    have := (h_le_iff k _).2 hr.2
    have := hr.1
    unfold absStart; omega
  · intro h
    unfold absStart at h
    exact le_mode ⟨by omega, (h_le_iff k _).1 (by omega)⟩

private theorem t_step (n : ℕ) : mode n ≤ mode (n + 1) ∧ mode (n + 1) ≤ mode n + 1 := by
  have h := HermiteAbsoluteMode.result.2 n
  have h1 := (mode_rises n).1
  have h2 := (mode_rises (n + 1)).1
  simp only [b] at h
  push_cast [h1, h2] at h
  omega

private theorem abs_diff_iff (n : ℕ) : (b (n + 1) : ℤ) - b n = -1 ↔ ∃ k, absStart k = n + 1 := by
  have hs := t_step n
  have h1 := (mode_rises n).1
  have h2 := (mode_rises (n + 1)).1
  have hd : (b (n + 1) : ℤ) - b n = 1 - 2 * ((mode (n + 1) : ℤ) - mode n) := by
    simp only [b]; push_cast [h1, h2]; ring
  rw [hd]
  constructor
  · intro h
    refine ⟨mode (n + 1), ?_⟩
    have hle := (le_t_iff (n + 1) (mode (n + 1))).1 le_rfl
    have hgt : ¬ absStart (mode (n + 1)) ≤ n := fun hh => by
      have := (le_t_iff n _).2 hh; omega
    omega
  · rintro ⟨k, hk⟩
    have hle := (le_t_iff (n + 1) k).2 (le_of_eq hk)
    have hgt : ¬ k ≤ mode n := fun hh => by have := (le_t_iff n k).1 hh; omega
    omega

private theorem h_step (k : ℕ) : hOffset k ≤ hOffset (k + 1) ∧ hOffset (k + 1) ≤ hOffset k + 1 := by
  have hj := (h_le_iff k (hOffset k)).1 le_rfl
  constructor
  · exact (h_le_iff k _).2 ((h_le_iff (k + 1) _).1 le_rfl |>.trans' (by omega))
  · apply (h_le_iff (k + 1) _).2
    unfold second at hj ⊢
    nlinarith

private theorem abs_start_step (k : ℕ) : absStart (k + 1) = absStart k + 2 ∨ absStart (k + 1) = absStart k + 3 := by
  have := h_step k; unfold absStart; omega

private theorem abs_start_zero : absStart 0 = 0 := by simp [absStart, hOffset, second]

private theorem h_one : hOffset 1 = 1 := by
  apply le_antisymm
  · exact (h_le_iff 1 1).2 (by decide)
  · by_contra h; push Not at h
    have := (h_le_iff 1 0).1 (by omega); simp [second] at this

private theorem abs_start_one : absStart 1 = 3 := by unfold absStart; rw [h_one]

/-- `L_j = ⌊(j + 1)(j + 2)/4⌋`. -/
def L (j : ℕ) : ℕ := second j / 4

private theorem h_L (j : ℕ) : hOffset (L j) = j := by
  apply le_antisymm
  · exact (h_le_iff _ _).2 (by unfold L; omega)
  · by_contra h; push Not at h
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 := (h_le_iff (L (i + 1)) i).1 (by omega)
    have h2 : second i + 2 * i + 4 = second (i + 1) := by unfold second; ring
    have hev : second (i + 1) % 2 = 0 := by
      unfold second; rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
    unfold L at h1
    omega

private theorem three_iff (k : ℕ) : absStart (k + 1) = absStart k + 3 ↔ ∃ j, k = L j := by
  have hs := h_step k
  unfold absStart
  constructor
  · intro h
    refine ⟨hOffset k, ?_⟩
    have hj := (h_le_iff k (hOffset k)).1 le_rfl
    have hnot : ¬ 4 * (k + 1) ≤ second (hOffset k) := fun hh => by
      have := (h_le_iff (k + 1) _).2 hh; omega
    unfold L; omega
  · rintro ⟨j, rfl⟩
    rw [h_L j]
    have hnot : ¬ 4 * (L j + 1) ≤ second j := by unfold L; omega
    have hne : hOffset (L j + 1) ≠ j := fun hh => hnot ((h_le_iff (L j + 1) j).1 (le_of_eq hh))
    have := h_step (L j)
    rw [h_L j] at this
    omega

private theorem abs_start_L (j : ℕ) : absStart (L j) = 2 * L j + j := by unfold absStart; rw [h_L j]

private theorem L_mono {i j : ℕ} (h : i ≤ j) : L i ≤ L j := Nat.div_le_div_right (second_mono h)

private theorem two_between (j r : ℕ) (h1 : L j < r) (h2 : r < L (j + 1)) :
    absStart (r + 1) = absStart r + 2 := by
  rcases abs_start_step r with h | h
  · exact h
  · obtain ⟨i, rfl⟩ := (three_iff r).1 h
    rcases Nat.lt_or_ge j i with hji | hji
    · have := L_mono (show j + 1 ≤ i by omega); omega
    · have := L_mono hji; omega

private theorem unique_iff (k : ℕ) :
    (∃! j, IsAbsMax k j) ↔ ¬ ∃ m, 1 ≤ m ∧ (k : ℤ) = a m := by
  obtain ⟨-, hmono, htie⟩ := HermiteAbsoluteTieOrders.result
  constructor
  · rintro ⟨j, hj, huniq⟩ ⟨m, hm, hk⟩
    have hT : HasExactlyTwo k := (htie k).2 ⟨m, ⟨hm, hk⟩, fun m' ⟨hm', hk'⟩ => by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := hmono m' m hm' h; omega
      · have := hmono m m' hm h; omega⟩
    obtain ⟨u, v, huv, huvs⟩ := hT
    have hu := huniq u ((huvs u).2 (Or.inl rfl))
    have hv := huniq v ((huvs v).2 (Or.inr rfl))
    omega
  · intro hn
    rcases unique_or_two k with h | h
    · exact h
    · obtain ⟨m, ⟨hm, hk⟩, -⟩ := (htie k).1 h
      exact absurd ⟨m, hm, hk⟩ hn

/-- The signed maximum `B(n)`, the coefficient at the signed mode. -/
noncomputable def signedMax (n : ℕ) : ℚ :=
  (HermiteSignedMode.physicistsHermite n).coeff (HermiteSignedMode.a n)

/-- The absolute maximum `M(n)`. -/
noncomputable def absMax (n : ℕ) : ℚ := |(HermiteSignedMode.physicistsHermite n).coeff (b n)|

private theorem signedMax_eq (n : ℕ) : signedMax n = weight n (2 * HermiteSignedMode.mode n) := by
  have hq := (HermiteSignedMode.mode_rises n).1
  have e := signed_eq n (2 * HermiteSignedMode.mode n) (by omega)
  rw [pow_mul, neg_one_sq, one_pow, one_mul,
    show n - 2 * (2 * HermiteSignedMode.mode n) = HermiteSignedMode.a n by
      unfold HermiteSignedMode.a; omega] at e
  rw [signedMax, HermiteSignedMode.polynomial_coeff n (HermiteSignedMode.a n) (Nat.sub_le _ _), e]

private theorem absMax_eq (n : ℕ) : absMax n = weight n (mode n) := by
  rw [absMax, HermiteSignedMode.polynomial_coeff n (b n) (Nat.sub_le _ _)]; rfl

/-- Theorem 3 and Corollary 4 of Ma and Zhang on OEIS A381524/A381737, with `t(n) = mode n` and
`b(n) = n - 2t(n)`: the quadratic threshold for `b`; at most two absolute maxima, a unique one
exactly off the tie degrees; the floor formula for `t`; `-5/2 < b(n) - √(2n) < 2`; the block
structure of the differences of `b` with starts `m_k = 2k + h_k`, long blocks exactly at
`L_j = ⌊(j + 1)(j + 2)/4⌋` starting at `2L_j + j`; at a tie degree the maximizing exponents are
`b` and `b + 2`, with opposite signs, and `B = M`; `B = M` exactly at tie degrees or when `t` is
even; and the signed mode `a` lies in `{b - 2, b, b + 2}`. -/
theorem result :
    (∀ n : ℕ, b n % 2 = n % 2 ∧
      ∀ j : ℕ, j % 2 = n % 2 → (b n ≤ j ↔ 2 * n ≤ j ^ 2 + 5 * j + 2)) ∧
    (∀ k : ℕ, (∃! j, IsAbsMax k j) ∨ HasExactlyTwo k) ∧
    (∀ k : ℕ, (∃! j, IsAbsMax k j) ↔ ¬ ∃ m, 1 ≤ m ∧ (k : ℤ) = a m) ∧
    (∀ n : ℕ, ⌊((2 * n + 5 : ℝ) - √(8 * n + 17)) / 4⌋ = (mode n : ℤ)) ∧
    (∀ n : ℕ, -(5 / 2 : ℝ) < (b n : ℝ) - √(2 * n) ∧ (b n : ℝ) - √(2 * n) < 2) ∧
    (∀ n k : ℕ, k ≤ mode n ↔ absStart k ≤ n) ∧
    (∀ n : ℕ, (b (n + 1) : ℤ) - b n = -1 ↔ ∃ k, absStart k = n + 1) ∧
    absStart 0 = 0 ∧ absStart 1 = 3 ∧
    (∀ k : ℕ, absStart (k + 1) = absStart k + 2 ∨ absStart (k + 1) = absStart k + 3) ∧
    (∀ k : ℕ, absStart (k + 1) = absStart k + 3 ↔ ∃ j, k = L j) ∧
    (∀ j : ℕ, absStart (L j) = 2 * L j + j) ∧
    (∀ j r : ℕ, L j < r → r < L (j + 1) → absStart (r + 1) = absStart r + 2) ∧
    (∀ n : ℕ, HasExactlyTwo n →
      (∀ j, IsAbsMax n j ↔ j = b n ∨ j = b n + 2) ∧
      (HermiteSignedMode.physicistsHermite n).coeff (b n) *
        (HermiteSignedMode.physicistsHermite n).coeff (b n + 2) < 0 ∧
      signedMax n = absMax n) ∧
    (∀ n : ℕ, signedMax n = absMax n ↔ HasExactlyTwo n ∨ Even (mode n)) ∧
    (∀ n : ℕ, HermiteSignedMode.a n = b n - 2 ∨ HermiteSignedMode.a n = b n ∨
      HermiteSignedMode.a n = b n + 2) := by
  refine ⟨fun n => ⟨by have := (mode_rises n).1; unfold b; omega, threshold_iff n⟩, unique_or_two,
    unique_iff, t_floor, b_growth, le_t_iff, abs_diff_iff, abs_start_zero, abs_start_one,
    abs_start_step, three_iff, abs_start_L, two_between,
    fun n hT => ⟨(tie_structure n hT).1, (tie_structure n hT).2, by
      rw [signedMax_eq, absMax_eq]; exact (B_eq_iff n).2 (Or.inl hT)⟩,
    fun n => by rw [signedMax_eq, absMax_eq]; exact B_eq_iff n, fun n => ?_⟩
  have hi := interlace n
  have hq := (HermiteSignedMode.mode_rises n).1
  have ht := (mode_rises n).1
  unfold HermiteSignedMode.a b
  omega

end D5.S3.Analytic.Polynomial.HermiteAbsoluteModeBlocks
