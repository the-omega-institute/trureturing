/- GID: D5/S3/Combinatorics/Circle/ThreeBitSourceQTwo
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeBitSourceQTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex]
   utility: none
   digest: Source-forced paired bits and exact wrap counts when the middle ladder is empty. -/
module
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
/-! Exact Q=2 source windows and their legal singleton exits. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem bit_of_interval (n e t : ℕ)
    (hlo : t * 2 ^ e ≤ n) (hhi : n < (t + 1) * 2 ^ e) (ht : t % 2 = 1) :
    n.testBit e = true := by
  have hd : n / 2 ^ e = t := by
    have h0 := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ e)).mpr hlo
    have h1 := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ e)).mpr hhi
    omega
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hd, ht]

/-- Both Q=2 candidates are present in the exact unused source mask. -/
theorem source_q_two_bits (x l : ℕ) (hx : 2 ≤ x) (hl : 2 ≤ l) :
    let P := 2 ^ x
    let K := 2 ^ l
    let n := K * P * (P + 1) / (2 * (1 + 3 * P))
    n.testBit (l - 2) = true ∧
      ((P % 12 = 4 ∧ n.testBit (l - 1) = true) ∨
        (P % 12 = 8 ∧ n.testBit l = true)) := by
  dsimp only
  let P := 2 ^ x
  let K := 2 ^ l
  let K4 := 2 ^ (l - 2)
  let j := P / 12
  let B := 2 * K * j
  let d := 2 * (1 + 3 * P)
  let A := K * P * (P + 1)
  let n := A / d
  change n.testBit (l - 2) = true ∧
    ((P % 12 = 4 ∧ n.testBit (l - 1) = true) ∨
      (P % 12 = 8 ∧ n.testBit l = true))
  have hK : K = 4 * K4 := by
    dsimp [K, K4]
    rw [show l = (l - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hKhalf : 2 ^ (l - 1) = 2 * K4 := by
    rw [show l - 1 = (l - 2) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hK4 : 0 < K4 := by dsimp [K4]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hP4 : P % 4 = 0 := by
    dsimp [P]
    rw [show x = 2 + (x - 2) by omega, pow_add]
    simp [Nat.mul_mod]
  have hP3 : P % 3 ≠ 0 := by
    intro hn
    have hc : Nat.Coprime 3 P := (by decide : Nat.Coprime 3 2).pow_right x
    have he := hc.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero hn)
    omega
  have hcases : P % 12 = 4 ∨ P % 12 = 8 := by omega
  rcases hcases with hPe | hPo
  · have hP : P = 12 * j + 4 := by
      have he := Nat.mod_add_div P 12
      dsimp [j]
      omega
    have helo : A = d * (B + 3 * K4) + K4 * (8 * j + 2) := by
      dsimp [A, d, B]
      rw [hP, hK]
      ring
    have hehi : d * (B + 4 * K4) = A + K4 * (64 * j + 24) := by
      dsimp [A, d, B]
      rw [hP, hK]
      ring
    have hnlo : B + 3 * K4 ≤ n := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      nlinarith only [helo]
    have hnhi : n < B + 4 * K4 := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have hp : 0 < K4 * (64 * j + 24) := by positivity
      nlinarith only [hehi, hp]
    have hb0 : n.testBit (l - 2) = true := by
      apply bit_of_interval n (l - 2) (8 * j + 3)
      · change (8 * j + 3) * K4 ≤ n
        have he : (8 * j + 3) * K4 = B + 3 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; exact hnlo
      · change n < (8 * j + 3 + 1) * K4
        have he : (8 * j + 3 + 1) * K4 = B + 4 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; exact hnhi
      · omega
    have hb1 : n.testBit (l - 1) = true := by
      apply bit_of_interval n (l - 1) (4 * j + 1)
      · rw [hKhalf]
        have he : (4 * j + 1) * (2 * K4) = B + 2 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; omega
      · rw [hKhalf]
        have he : (4 * j + 1 + 1) * (2 * K4) = B + 4 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; exact hnhi
      · omega
    exact ⟨hb0, Or.inl ⟨hPe, hb1⟩⟩
  · have hP : P = 12 * j + 8 := by
      have he := Nat.mod_add_div P 12
      dsimp [j]
      omega
    have helo : A = d * (B + 5 * K4) + K4 * (56 * j + 38) := by
      dsimp [A, d, B]
      rw [hP, hK]
      ring
    have hehi : d * (B + 6 * K4) = A + K4 * (16 * j + 12) := by
      dsimp [A, d, B]
      rw [hP, hK]
      ring
    have hnlo : B + 5 * K4 ≤ n := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      nlinarith only [helo]
    have hnhi : n < B + 6 * K4 := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have hp : 0 < K4 * (16 * j + 12) := by positivity
      nlinarith only [hehi, hp]
    have hb0 : n.testBit (l - 2) = true := by
      apply bit_of_interval n (l - 2) (8 * j + 5)
      · change (8 * j + 5) * K4 ≤ n
        have he : (8 * j + 5) * K4 = B + 5 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; exact hnlo
      · change n < (8 * j + 5 + 1) * K4
        have he : (8 * j + 5 + 1) * K4 = B + 6 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; exact hnhi
      · omega
    have hb1 : n.testBit l = true := by
      apply bit_of_interval n l (2 * j + 1)
      · change (2 * j + 1) * K ≤ n
        have he : (2 * j + 1) * K = B + 4 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; omega
      · change n < (2 * j + 1 + 1) * K
        have he : (2 * j + 1 + 1) * K = B + 8 * K4 := by dsimp [B]; rw [hK]; ring
        rw [he]; omega
      · omega
    exact ⟨hb0, Or.inr ⟨hPo, hb1⟩⟩

private theorem q_two_low (P : ℤ) (hP : 4 ≤ P) :
    let u := 1 + 3 * P
    let w := 3 + 8 * P
    4 * P - 3 * P + 1 ≤ u % w ∧ u % w ≤ w - u := by
  dsimp only
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

private theorem q_two_even (P r : ℤ) (hP : 4 ≤ P) (hr : 4 ≤ r) :
    let u := 1 + 3 * P
    let w := 3 + 4 * r * P
    2 * r * P - 3 * P + 1 ≤ (r * u) % w ∧ (r * u) % w ≤ w - u := by
  dsimp only
  have hp := mul_nonneg (show 0 ≤ r - 4 by omega) (show 0 ≤ P - 1 by omega)
  have hpos := mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ P by omega)
  have hbound : r * (1 + 3 * P) ≤ (3 + 4 * r * P) - (1 + 3 * P) := by nlinarith
  have hs0 : 0 ≤ r * (1 + 3 * P) := by positivity
  have hs1 : r * (1 + 3 * P) < 3 + 4 * r * P := by nlinarith
  rw [Int.emod_eq_of_lt hs0 hs1]
  exact ⟨by nlinarith, hbound⟩

private theorem q_two_odd (P K : ℤ) (hP : 8 ≤ P) (hK : 8 ≤ K) :
    let R := K * P
    let u := 1 + 3 * P
    let w := 3 + 2 * R
    R - 3 * P + 1 ≤ (K * u) % w ∧ (K * u) % w ≤ w - u := by
  dsimp only
  let R := K * P
  let w := 3 + 2 * R
  let τ := -R + K - 6
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hhalf : w / 2 = R + 1 := by dsimp [w]; omega
  have hτlo : -(w / 2) ≤ τ := by rw [hhalf]; dsimp [τ]; omega
  have hτneg : τ < 0 := by
    have hm := mul_nonneg (show 0 ≤ K by omega) (show 0 ≤ P - 1 by omega)
    dsimp [τ, R]; nlinarith only [hm]
  have hs0 : 0 ≤ τ + w := by omega
  have hs1 : τ + w < w := by omega
  have htwo : K * (1 + 3 * P) = (τ + w) + w := by dsimp [τ, w, R]; ring
  change R - 3 * P + 1 ≤ (K * (1 + 3 * P)) % w ∧
    (K * (1 + 3 * P)) % w ≤ w - (1 + 3 * P)
  rw [htwo, Int.add_emod_right, Int.emod_eq_of_lt hs0 hs1]
  constructor
  · dsimp [τ, w]; omega
  · have hm := mul_nonneg (show 0 ≤ K - 4 by omega) (show 0 ≤ P - 1 by omega)
    dsimp [τ, w, R]; nlinarith

/-- The Q=2 exit uses a source-forced singleton; the odd branch retains its double wrap. -/
theorem q_two_selected_bit (x l : ℕ) (hx : 2 ≤ x) (hl : 2 ≤ l) :
    let n := 2 ^ l * 2 ^ x * (2 ^ x + 1) / (2 * (1 + 3 * 2 ^ x))
    let P : ℤ := 2 ^ x
    let K : ℤ := 2 ^ l
    let u := 1 + 3 * P
    let w := 3 + 2 * K * P
    ∃ e : ℕ, e ≤ l ∧ n.testBit e = true ∧
      K * P - 3 * P + 1 ≤ ((2 : ℤ) ^ e * u) % w ∧
      ((2 : ℤ) ^ e * u) % w ≤ w - u := by
  dsimp only
  let P : ℤ := 2 ^ x
  let K : ℤ := 2 ^ l
  let u := 1 + 3 * P
  let w := 3 + 2 * K * P
  let n := 2 ^ l * 2 ^ x * (2 ^ x + 1) / (2 * (1 + 3 * 2 ^ x))
  change ∃ e, e ≤ l ∧ n.testBit e = true ∧
    K * P - 3 * P + 1 ≤ ((2 : ℤ) ^ e * u) % w ∧ ((2 : ℤ) ^ e * u) % w ≤ w - u
  obtain ⟨hb0, hb1⟩ := source_q_two_bits x l hx hl
  change n.testBit (l - 2) = true at hb0
  have hP : 4 ≤ P := by
    dsimp [P]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hx
  by_cases hl2 : l = 2
  · subst l
    refine ⟨0, by omega, by simpa using hb0, ?_, ?_⟩
    · simpa [P, K, u, w] using (q_two_low ((2 : ℤ) ^ x) hP).1
    · simpa [P, K, u, w] using (q_two_low ((2 : ℤ) ^ x) hP).2
  · have hl3 : 3 ≤ l := by omega
    have hK8 : 8 ≤ K := by
      dsimp [K]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hl3
    rcases hb1 with ⟨he, hb⟩ | ⟨ho, hb⟩
    · let r : ℤ := 2 ^ (l - 1)
      have hr : 4 ≤ r := by
        dsimp [r]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 2 ≤ l - 1 by omega)
      have hK : K = 2 * r := by
        dsimp [K, r]
        conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ]
        ring
      have hres := q_two_even P r hP hr
      have hw : w = 3 + 4 * r * P := by dsimp [w]; rw [hK]; ring
      refine ⟨l - 1, by omega, hb, ?_, ?_⟩
      · change K * P - 3 * P + 1 ≤ (r * u) % w
        rw [hK, hw]
        exact hres.1
      · change (r * u) % w ≤ w - u
        rw [hw]
        exact hres.2
    · have hp8 : 8 ≤ P := by
        have hm := Nat.mod_le (2 ^ x) 12
        rw [ho] at hm
        dsimp only [P]
        exact_mod_cast hm
      have hres := q_two_odd P K hp8 hK8
      refine ⟨l, le_rfl, hb, ?_, ?_⟩
      · simpa only [u, w, mul_assoc] using hres.1
      · simpa only [u, w, mul_assoc] using hres.2

end D5.S3.Combinatorics.Circle.ThreeBitSource
