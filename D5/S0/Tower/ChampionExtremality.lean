/- GID: D5/S0/Tower/ChampionExtremality
   generality: G
   mirror-B: D5/B/S0/Tower/ChampionExtremality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer radix towers have exact odd and even champion arms. -/

import D5.S0.Tower.ConstantArms

namespace D5.S0.Tower.ChampionExtremality

open D5.S0.Tower.ConstantArms

/-- Above the even-radix champion threshold, one multiplication by the radix exits below it. -/
theorem one_step_exit (b : ℕ) (hb : 2 ≤ b) (hbEven : Even b) (y : ℝ)
    (hy : radixDistance b 0 y > (b : ℝ) / (2 * (b + 1))) :
    radixDistance b 0 ((b : ℝ) * y) < (b : ℝ) / (2 * (b + 1)) := by
  rcases hbEven with ⟨k, rfl⟩
  have hk : 1 ≤ k := by omega
  let c : ℝ := ((k + k : ℕ) : ℝ) / (2 * (((k + k : ℕ) : ℝ) + 1))
  let d : ℝ := y - (round y : ℝ)
  have hy' : c < |d| := by
    simpa [c, d, radixDistance] using hy
  have hd_le : |d| ≤ (1 : ℝ) / 2 := by
    simpa [d] using abs_sub_round y
  have hbc : (((k + k : ℕ) : ℝ) * c) = (k : ℝ) - c := by
    dsimp [c]
    field_simp
    push_cast
    ring
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hb_pos : 0 < ((k + k : ℕ) : ℝ) := by positivity
  simp only [radixDistance, pow_zero, one_mul, div_one]
  change |((k + k : ℕ) : ℝ) * y -
      (round (((k + k : ℕ) : ℝ) * y) : ℝ)| < c
  rcases le_total 0 d with hd_nonneg | hd_nonpos
  · have hdc : c < d := by simpa [abs_of_nonneg hd_nonneg] using hy'
    have hd_half : d ≤ (1 : ℝ) / 2 := (le_abs_self d).trans hd_le
    have hdiff_nonneg :
        0 ≤ (k : ℝ) - ((k + k : ℕ) : ℝ) * d := by
      push_cast
      nlinarith
    calc
      |((k + k : ℕ) : ℝ) * y - (round (((k + k : ℕ) : ℝ) * y) : ℝ)| ≤
          |((k + k : ℕ) : ℝ) * y -
            ((((k + k : ℕ) : ℤ) * round y + k : ℤ) : ℝ)| :=
        round_le (((k + k : ℕ) : ℝ) * y)
          (((k + k : ℕ) : ℤ) * round y + k)
      _ = |((k + k : ℕ) : ℝ) * d - (k : ℝ)| := by
        dsimp [d]
        push_cast
        congr 1
        ring
      _ = (k : ℝ) - ((k + k : ℕ) : ℝ) * d := by
        rw [abs_of_nonpos]
        · ring
        · linarith
      _ = c + ((k + k : ℕ) : ℝ) * (c - d) := by nlinarith [hbc]
      _ < c := by
        have : ((k + k : ℕ) : ℝ) * (c - d) < 0 :=
          mul_neg_of_pos_of_neg hb_pos (sub_neg.mpr hdc)
        linarith
  · have hd_neg : d < 0 := by
      apply lt_of_le_of_ne hd_nonpos
      intro hd_zero
      have habs_zero : |d| = 0 := abs_eq_zero.mpr hd_zero
      linarith
    have hdc : d < -c := by
      rw [abs_of_neg hd_neg] at hy'
      linarith
    have hneg_half : -(1 : ℝ) / 2 ≤ d := by
      have := (neg_le_neg hd_le).trans (neg_abs_le d)
      nlinarith
    have hdiff_nonneg :
        0 ≤ ((k + k : ℕ) : ℝ) * d + (k : ℝ) := by
      push_cast
      nlinarith
    calc
      |((k + k : ℕ) : ℝ) * y - (round (((k + k : ℕ) : ℝ) * y) : ℝ)| ≤
          |((k + k : ℕ) : ℝ) * y -
            ((((k + k : ℕ) : ℤ) * round y - k : ℤ) : ℝ)| :=
        round_le (((k + k : ℕ) : ℝ) * y)
          (((k + k : ℕ) : ℤ) * round y - k)
      _ = |((k + k : ℕ) : ℝ) * d + (k : ℝ)| := by
        dsimp [d]
        push_cast
        congr 1
        ring
      _ = ((k + k : ℕ) : ℝ) * d + (k : ℝ) := abs_of_nonneg hdiff_nonneg
      _ = c + ((k + k : ℕ) : ℝ) * (d + c) := by nlinarith [hbc]
      _ < c := by
        have hdc' : d + c < 0 := by linarith
        have : ((k + k : ℕ) : ℝ) * (d + c) < 0 :=
          mul_neg_of_pos_of_neg hb_pos hdc'
        linarith

/-- The supremum of eventual normalized lower bounds for an even radix is its champion arm. -/
theorem even_champion_sup (b : ℕ) (hb : 2 ≤ b) (hbEven : Even b) :
    sSup {r : ℝ | ∃ x : ℝ, ∃ N : ℕ, ∀ Q ≥ N,
      r ≤ (b : ℝ) ^ Q * radixDistance b Q x} =
      (b : ℝ) / (2 * (b + 1)) := by
  let c : ℝ := (b : ℝ) / (2 * (b + 1))
  let S : Set ℝ := {r | ∃ x : ℝ, ∃ N : ℕ, ∀ Q ≥ N,
    r ≤ (b : ℝ) ^ Q * radixDistance b Q x}
  change sSup S = c
  have hb0 : b ≠ 0 := by omega
  have hc_mem : c ∈ S := by
    refine ⟨(((b / 2 : ℕ) : ℝ) / (b + 1)), 1, ?_⟩
    intro Q hQ
    have harm := even_champion_arm b Q hb hQ hbEven
    simpa [c] using harm.ge
  have hupper : ∀ r ∈ S, r ≤ c := by
    intro r hr
    rcases hr with ⟨x, N, hN⟩
    by_contra hrc
    have hcr : c < r := lt_of_not_ge hrc
    have hb0r : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
    have hscaled (Q : ℕ) :
        (b : ℝ) ^ Q * radixDistance b Q x =
          radixDistance b 0 ((b : ℝ) ^ Q * x) := by
      unfold radixDistance
      rw [mul_div_cancel₀ _ (pow_ne_zero Q hb0r)]
      simp
    have hy : c < radixDistance b 0 ((b : ℝ) ^ N * x) := by
      rw [← hscaled N]
      exact hcr.trans_le (hN N le_rfl)
    have hexit := one_step_exit b hb hbEven ((b : ℝ) ^ N * x) hy
    have hnext : c < (b : ℝ) ^ (N + 1) * radixDistance b (N + 1) x :=
      hcr.trans_le (hN (N + 1) (Nat.le_succ N))
    rw [hscaled (N + 1)] at hnext
    have hpow : (b : ℝ) ^ (N + 1) * x = (b : ℝ) * ((b : ℝ) ^ N * x) := by
      rw [pow_succ]
      ring
    rw [hpow] at hnext
    exact (not_lt_of_ge hnext.le) hexit
  exact le_antisymm
    (csSup_le ⟨c, hc_mem⟩ hupper)
    (le_csSup ⟨c, hupper⟩ hc_mem)

/-- For an odd radix, the half point stays exactly half a grid spacing from every level. -/
theorem odd_half_arm (b Q : ℕ) (hb : 2 ≤ b) (hbOdd : Odd b) :
    (b : ℝ) ^ Q * radixDistance b Q (1 / 2) = 1 / 2 := by
  have hb0r : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [radixDistance, mul_div_cancel₀ _ (pow_ne_zero Q hb0r)]
  have hmod : b ^ Q % 2 = 1 := Nat.odd_iff.mp hbOdd.pow
  have hround := abs_sub_round_div_natCast_eq (α := ℝ) (m := b ^ Q) (n := 2)
  norm_num [hmod] at hround
  simpa [div_eq_mul_inv] using hround

/-- The supremum of eventual normalized lower bounds for an odd radix is one half. -/
theorem odd_champion (b : ℕ) (hb : 2 ≤ b) (hbOdd : Odd b) :
    sSup {r : ℝ | ∃ x : ℝ, ∃ N : ℕ, ∀ Q ≥ N,
      r ≤ (b : ℝ) ^ Q * radixDistance b Q x} = 1 / 2 := by
  let S : Set ℝ := {r | ∃ x : ℝ, ∃ N : ℕ, ∀ Q ≥ N,
    r ≤ (b : ℝ) ^ Q * radixDistance b Q x}
  change sSup S = 1 / 2
  have hb0r : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hhalf_mem : (1 / 2 : ℝ) ∈ S := by
    refine ⟨1 / 2, 0, ?_⟩
    intro Q _hQ
    exact (odd_half_arm b Q hb hbOdd).ge
  have hupper : ∀ r ∈ S, r ≤ (1 / 2 : ℝ) := by
    intro r hr
    rcases hr with ⟨x, N, hN⟩
    refine (hN N le_rfl).trans ?_
    unfold radixDistance
    rw [mul_div_cancel₀ _ (pow_ne_zero N hb0r)]
    exact abs_sub_round ((b : ℝ) ^ N * x)
  exact le_antisymm
    (csSup_le ⟨1 / 2, hhalf_mem⟩ hupper)
    (le_csSup ⟨1 / 2, hupper⟩ hhalf_mem)

end D5.S0.Tower.ChampionExtremality
