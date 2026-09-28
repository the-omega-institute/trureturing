/- GID: D5/S3/Observer/Prediction/BoundedRationalReadout
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/BoundedRationalReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clipped readouts have uniform error and separate storage bounds. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Prediction.BoundedRationalReadout

/-- The full signed report count, with true denoting a one report. -/
def balance (w : List Bool) : ℤ :=
  (w.map (fun x => if x then (1 : ℤ) else -1)).sum

noncomputable def exactReadout (b : ℤ) : ℝ :=
  1 / 4 + (3 : ℝ) ^ b / (2 * (1 + (3 : ℝ) ^ b))

/-- Only the readout is clipped; the integer state is retained. -/
noncomputable def clippedReadout (K : ℕ) (b : ℤ) : ℝ :=
  if b ≤ -(K : ℤ) then 1 / 4 else
  if (K : ℤ) ≤ b then 3 / 4 else exactReadout b

noncomputable def tailError (K : ℕ) : ℝ := 1 / (2 * (1 + (3 : ℝ) ^ K))

/-- Unreduced, positive integer fractions suffice for exact output encoding. -/
def exactFraction (b : ℤ) : ℕ × ℕ :=
  (if b < 0 then 3 ^ b.natAbs + 3 else 1 + 3 ^ (b.natAbs + 1),
   4 * (1 + 3 ^ b.natAbs))

def outputFraction (K : ℕ) (b : ℤ) : ℕ × ℕ :=
  if b ≤ -(K : ℤ) then (1, 4) else
  if (K : ℤ) ≤ b then (3, 4) else exactFraction b

/-- The literal table contains each interior balance once in increasing order. -/
def interiorTable (K : ℕ) (i : Fin (2 * K - 1)) : ℕ × ℕ :=
  exactFraction ((i.val : ℤ) - ((K : ℤ) - 1))

/-- Each of the two fields in a table cell has fixed width 2K+4. -/
def tableBits (K : ℕ) : ℕ := (2 * K - 1) * (2 * (2 * K + 4))

/-- One sign bit followed by the binary magnitude. -/
def balanceBits (b : ℤ) : ℕ := 1 + b.natAbs.bits.length

/-- Uniform clipping, explicit fraction and table bounds, and retained evidence.
The final clause rules out updating the clipped output alone. -/
theorem uniform_tail_clip_error_and_bit_budget
    (K : ℕ) (hK : 1 ≤ K) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1 / 4)
    (hδ : tailError K ≤ ε) :
    (∀ b : ℤ, exactReadout (-b) = 1 - exactReadout b) ∧
    (∀ b : ℤ, (K : ℤ) ≤ b →
      3 / 4 - exactReadout b = 1 / (2 * (1 + (3 : ℝ) ^ b)) ∧
      0 ≤ 3 / 4 - exactReadout b ∧ 3 / 4 - exactReadout b ≤ tailError K) ∧
    (∀ b : ℤ, b ≤ -(K : ℤ) →
      exactReadout b - 1 / 4 = 1 / (2 * (1 + (3 : ℝ) ^ (-b))) ∧
      0 ≤ exactReadout b - 1 / 4 ∧ exactReadout b - 1 / 4 ≤ tailError K) ∧
    (∀ w : List Bool, |clippedReadout K (balance w) - exactReadout (balance w)| ≤ ε) ∧
    (∀ b : ℤ, 0 < (outputFraction K b).2 ∧
      ((outputFraction K b).1 : ℝ) / (outputFraction K b).2 = clippedReadout K b ∧
      (outputFraction K b).1.bits.length ≤ 2 * K + 4 ∧
      (outputFraction K b).2.bits.length ≤ 2 * K + 4) ∧
    (∀ i : Fin (2 * K - 1),
      0 < (interiorTable K i).2 ∧
      ((interiorTable K i).1 : ℝ) / (interiorTable K i).2 =
        exactReadout ((i.val : ℤ) - ((K : ℤ) - 1)) ∧
      (interiorTable K i).1 < 2 ^ (2 * K + 4) ∧
      (interiorTable K i).2 < 2 ^ (2 * K + 4)) ∧
    tableBits K ≤ 24 * K ^ 2 ∧
    balance [] = 0 ∧
    (∀ (w : List Bool) (x : Bool),
      balance (w ++ [x]) = balance w + (if x then 1 else -1)) ∧
    (∀ w : List Bool,
      balance w = (w.count true : ℤ) - w.count false ∧
      (balance w).natAbs ≤ w.length ∧
      balanceBits (balance w) ≤ 2 + Nat.log2 (w.length + 1)) ∧
    (¬ ∃ forecast : ℕ → ℝ → ℕ → ℝ, ∀ (w : List Bool) (n : ℕ),
      |forecast w.length (clippedReadout K (balance w)) n -
        exactReadout (balance w - (n : ℤ))| ≤ ε) ∧
    ¬ ∃ update : ℝ → Bool → ℝ, ∀ (b : ℤ) (x : Bool),
      update (clippedReadout K b) x =
        clippedReadout K (b + (if x then 1 else -1)) := by
  have hp (b : ℤ) : 0 < (3 : ℝ) ^ b := zpow_pos (by norm_num) b
  have hd (b : ℤ) : 1 + (3 : ℝ) ^ b ≠ 0 := ne_of_gt (by linarith [hp b])
  have symm (b : ℤ) : exactReadout (-b) = 1 - exactReadout b := by
    unfold exactReadout
    rw [zpow_neg]
    field_simp
    ring
  have tail (b : ℤ) : 3 / 4 - exactReadout b =
      1 / (2 * (1 + (3 : ℝ) ^ b)) := by
    unfold exactReadout
    field_simp [hd b]
    ring
  have upper (b : ℤ) (hb : (K : ℤ) ≤ b) :
      0 ≤ 3 / 4 - exactReadout b ∧ 3 / 4 - exactReadout b ≤ tailError K := by
    rw [tail]
    constructor
    · positivity
    · apply one_div_le_one_div_of_le (by positivity)
      have hm := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) hb
      simp only [zpow_natCast] at hm
      linarith
  have lower (b : ℤ) (hb : b ≤ -(K : ℤ)) :
      exactReadout b - 1 / 4 = 1 / (2 * (1 + (3 : ℝ) ^ (-b))) ∧
      0 ≤ exactReadout b - 1 / 4 ∧ exactReadout b - 1 / 4 ≤ tailError K := by
    have he : exactReadout b - 1 / 4 = 3 / 4 - exactReadout (-b) := by rw [symm]; ring
    rw [he]
    exact ⟨tail (-b), upper (-b) (by omega)⟩
  have fraction (b : ℤ) : 0 < (exactFraction b).2 ∧
      ((exactFraction b).1 : ℝ) / (exactFraction b).2 = exactReadout b := by
    constructor
    · simp only [exactFraction]; positivity
    · by_cases hb : b < 0
      · have he : b = -(b.natAbs : ℤ) := by omega
        simp only [exactFraction, if_pos hb]
        rw [he, symm]
        simp only [exactReadout, zpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, Nat.cast_one, Int.natAbs_neg, Int.natAbs_natCast]
        field_simp
        ring
      · have he : b = (b.natAbs : ℤ) := by omega
        simp only [exactFraction, if_neg hb]
        rw [he]
        simp only [exactReadout, zpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, Nat.cast_one, pow_succ, Int.natAbs_natCast]
        field_simp
        ring
  have small (b : ℤ) (hb : b.natAbs < K) :
      (exactFraction b).1 < 2 ^ (2 * K + 4) ∧
      (exactFraction b).2 < 2 ^ (2 * K + 4) := by
    have hpow : 3 ^ b.natAbs ≤ 2 ^ (2 * K) := by
      calc
        3 ^ b.natAbs ≤ (4 : ℕ) ^ b.natAbs := Nat.pow_le_pow_left (by omega) _
        _ ≤ 4 ^ K := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 2 ^ (2 * K) := by rw [pow_mul]; rfl
    have hpos : 0 < (2 : ℕ) ^ (2 * K) := by positivity
    simp only [exactFraction, pow_succ]
    split_ifs <;> constructor <;> nlinarith
  have hbnd (w : List Bool) :
      balance w = (w.count true : ℤ) - w.count false ∧
      (balance w).natAbs ≤ w.length := by
    induction w with
    | nil => simp [balance]
    | cons x w ih =>
      have hsum : balance (x :: w) = (if x then 1 else -1) + balance w := by
        simp [balance]
      rw [hsum]
      cases x <;> simp_all <;> omega
  refine ⟨symm, (fun b hb => ⟨tail b, upper b hb⟩), lower, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro w
    unfold clippedReadout
    split_ifs with hl hu
    · have hh := lower (balance w) hl
      rw [abs_of_nonpos (by linarith [hh.2.1])]
      linarith [hh.2.2]
    · have hh := upper (balance w) hu
      rw [abs_of_nonneg hh.1]
      exact hh.2.trans hδ
    · simpa using le_of_lt _hε
  · intro b
    unfold outputFraction clippedReadout
    split_ifs with hl hu
    · norm_num [show (1 : ℕ).bits.length = 1 from rfl,
        show (3 : ℕ).bits.length = 2 from rfl, show (4 : ℕ).bits.length = 3 from rfl]
    · norm_num [show (1 : ℕ).bits.length = 1 from rfl,
        show (3 : ℕ).bits.length = 2 from rfl, show (4 : ℕ).bits.length = 3 from rfl]
    · obtain ⟨hn, hd'⟩ := small b (by omega)
      exact ⟨(fraction b).1, (fraction b).2,
        (Nat.size_eq_bits_len _).trans_le (Nat.size_le.mpr hn),
        (Nat.size_eq_bits_len _).trans_le (Nat.size_le.mpr hd')⟩
  · intro i
    have hi := i.isLt
    have hsmall := small ((i.val : ℤ) - ((K : ℤ) - 1)) (by omega)
    exact ⟨(fraction _).1, (fraction _).2, hsmall⟩
  · unfold tableBits
    have hsub : 2 * K - 1 ≤ 2 * K := Nat.sub_le _ _
    calc
      (2 * K - 1) * (2 * (2 * K + 4)) ≤ 2 * K * (2 * (2 * K + 4)) :=
        Nat.mul_le_mul_right _ hsub
      _ ≤ 24 * K ^ 2 := by nlinarith
  · intro w x
    simp [balance]
  · intro w
    refine ⟨(hbnd w).1, (hbnd w).2, ?_⟩
    unfold balanceBits
    rw [Nat.size_eq_bits_len]
    have hsize : (balance w).natAbs.size ≤ Nat.log2 (w.length + 1) + 1 := by
      apply Nat.size_le.mpr
      exact lt_of_le_of_lt ((hbnd w).2.trans (Nat.le_succ _)) Nat.lt_log2_self
    omega
  · rintro ⟨forecast, hf⟩
    have hr : 0 < 1 / 4 - ε := by linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 / 4 - ε))
      (show (1 : ℝ) < 3 by norm_num)
    have hsep : 1 / (2 * (1 + (3 : ℝ) ^ n)) < 1 / 4 - ε := by
      apply (div_lt_iff₀ (by positivity)).2
      have hh := (div_lt_iff₀ hr).1 hn
      nlinarith [pow_pos (show (0 : ℝ) < 3 by norm_num) n]
    let w₁ := List.replicate (K + n) true ++ List.replicate n false
    let w₂ := List.replicate (K + 2 * n) true
    have hb₁ : balance w₁ = K := by simp [w₁, balance]
    have hb₂ : balance w₂ = (K : ℤ) + 2 * n := by simp [w₂, balance]
    have hl₁ : w₁.length = K + 2 * n := by simp [w₁]; omega
    have hl₂ : w₂.length = K + 2 * n := by simp [w₂]
    have hc₁ : clippedReadout K (balance w₁) = 3 / 4 := by
      rw [hb₁]
      simp [clippedReadout, show ¬ (K : ℤ) ≤ -(K : ℤ) by omega]
    have hc₂ : clippedReadout K (balance w₂) = 3 / 4 := by
      rw [hb₂]
      simp [clippedReadout, show ¬ (K : ℤ) + 2 * n ≤ -(K : ℤ) by omega,
        show (K : ℤ) ≤ (K : ℤ) + 2 * n by omega]
    have h₁ := hf w₁ (K + n)
    have h₂ := hf w₂ (K + n)
    rw [hl₁, hc₁, hb₁] at h₁
    rw [hl₂, hc₂, hb₂] at h₂
    have he₁ : (K : ℤ) - (↑(K + n) : ℤ) = -(n : ℤ) := by omega
    have he₂ : (K : ℤ) + 2 * n - (↑(K + n) : ℤ) = n := by omega
    rw [he₁, symm] at h₁
    rw [he₂] at h₂
    have ht := tail (n : ℤ)
    simp only [zpow_natCast] at ht
    have h₁' := (abs_le.mp h₁).2
    have h₂' := (abs_le.mp h₂).1
    linarith
  · rintro ⟨update, hu⟩
    have h1 := hu (K : ℤ) false
    have h2 := hu ((K : ℤ) + 1) false
    have hc : clippedReadout K (K : ℤ) = 3 / 4 := by
      simp [clippedReadout, show ¬ (K : ℤ) ≤ -(K : ℤ) by omega]
    have hc' : clippedReadout K ((K : ℤ) + 1) = 3 / 4 := by
      simp [clippedReadout, show ¬ (K : ℤ) + 1 ≤ -(K : ℤ) by omega]
    have hm : clippedReadout K ((K : ℤ) - 1) = exactReadout ((K : ℤ) - 1) := by
      simp [clippedReadout, show ¬ (K : ℤ) - 1 ≤ -(K : ℤ) by omega,
        show ¬ (K : ℤ) ≤ (K : ℤ) - 1 by omega]
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    rw [hc] at h1
    rw [hc'] at h2
    have he : (K : ℤ) + 1 + -1 = K := by omega
    rw [he, hc] at h2
    have he' : (K : ℤ) + -1 = (K : ℤ) - 1 := by omega
    rw [he', hm, h2] at h1
    have ht := tail ((K : ℤ) - 1)
    have hpositive : 0 < 1 / (2 * (1 + (3 : ℝ) ^ ((K : ℤ) - 1))) := by positivity
    linarith

end D5.S3.Observer.Prediction.BoundedRationalReadout
