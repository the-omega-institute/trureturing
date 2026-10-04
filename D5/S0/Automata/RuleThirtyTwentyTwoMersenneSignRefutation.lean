/- GID: D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation
   generality: I
   mirror-B: D5/B/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.claim; result=D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.result; claim=D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.claim
   digest: Refutes the Rule 30/22 Mersenne sign pattern at row 767. -/

/-
proof_shape: result: content; light_cone: content; encoding_bridge: content;
  support_encoded: content.
escape_witness: light_cone proves that a quiescent single-seed row vanishes outside [-m,m];
  encoding_bridge identifies row g m r with bitAt (step^[m] 1) (r + m) for every compatible
  bitwise step. Both inductions are used by support_encoded, which identifies the full-row
  support with the injective image i -> (i : Z)-m of its active encoded bits. The result
  uses this identification to obtain supportCard g30 767 = 763 and supportCard g22 767 = 768.
admission_basis: open-problem-resolution (#12739; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000
set_option autoImplicit false

namespace D5.S0.Automata.RuleThirtyTwentyTwoMersenneSignRefutation

/-- Single-seed evolution on the full integer lattice with left, centre and right arguments. -/
def row (g : Bool → Bool → Bool → Bool) : ℕ → ℤ → Bool
  | 0, r => decide (r = 0)
  | m + 1, r => g (row g m (r - 1)) (row g m r) (row g m (r + 1))

/-- The algebraic normal form of Rule 30 in Proposition 1. -/
def g30 (a b c : Bool) : Bool := a ^^ b ^^ c ^^ (b && c)
/-- The algebraic normal form of Rule 22 in equation (1). -/
def g22 (a b c : Bool) : Bool := a ^^ b ^^ c ^^ (a && b && c)
/-- Cardinality of the full-row support in Definition 2. -/
noncomputable def supportCard (g : Bool → Bool → Bool → Bool) (m : ℕ) : ℕ :=
  Set.ncard {r : ℤ | row g m r = true}
/-- Integer difference of the two full-row support cardinalities, equation (11). -/
noncomputable def eps (m : ℕ) : ℤ := (supportCard g30 m : ℤ) - (supportCard g22 m : ℤ)
/-- The all-row sign-pattern interpretation of Remark 3 and the question in section 9. -/
def claim : Prop := ∀ m : ℕ, 1 ≤ m → (eps m ≤ 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ m = 2 ^ k - 1)

private def bitAt (b : ℕ) (z : ℤ) : Bool := decide (0 ≤ z) && b.testBit z.toNat
private def step30 (b : ℕ) : ℕ := (b <<< 2) ^^^ ((b <<< 1) ||| b)
private def step22 (b : ℕ) : ℕ :=
  (b <<< 2) ^^^ (b <<< 1) ^^^ b ^^^ ((b <<< 2) &&& (b <<< 1) &&& b)

private theorem light_cone (g : Bool → Bool → Bool → Bool) (hg : g false false false = false)
    (m : ℕ) (r : ℤ) (h : r < -(m : ℤ) ∨ (m : ℤ) < r) : row g m r = false := by
  induction m generalizing r with
  | zero => simp [row, show r ≠ 0 by omega]
  | succ m ih =>
    rw [row, ih (r - 1) (by push_cast at h; omega), ih r (by push_cast at h; omega),
      ih (r + 1) (by push_cast at h; omega), hg]

private theorem encoding_bridge (g : Bool → Bool → Bool → Bool) (step : ℕ → ℕ)
    (hs : ∀ b z, bitAt (step b) z = g (bitAt b (z - 2)) (bitAt b (z - 1)) (bitAt b z))
    (m : ℕ) (r : ℤ) : row g m r = bitAt (step^[m] 1) (r + m) := by
  induction m generalizing r with
  | zero =>
    apply Bool.eq_iff_iff.mpr
    simp only [row, Function.iterate_zero_apply, Nat.cast_zero, add_zero, bitAt,
      Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega
  | succ m ih =>
    rw [row, Function.iterate_succ_apply', hs, ih (r - 1), ih r, ih (r + 1)]
    congr 1 <;> congr 1 <;> push_cast <;> ring

private theorem support_encoded (g : Bool → Bool → Bool → Bool) (step : ℕ → ℕ)
    (hg : g false false false = false)
    (hs : ∀ b z, bitAt (step b) z = g (bitAt b (z - 2)) (bitAt b (z - 1)) (bitAt b z))
    (m : ℕ) : supportCard g m = Nat.count (fun i => (step^[m] 1).testBit i = true) (2*m + 1) := by
  let window := (Finset.Icc (-(m : ℤ)) m).filter (fun r => row g m r = true)
  have hset : {r : ℤ | row g m r = true} = (window : Set ℤ) := by
    ext r
    simp only [window, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    constructor
    · intro hr
      have bounds : -(m : ℤ) ≤ r ∧ r ≤ m := by
        by_contra hn
        have hzero := light_cone g hg m r (by omega)
        simp [hzero] at hr
      exact ⟨bounds, hr⟩
    · exact And.right
  have hwindow : window =
      ((Finset.range (2*m + 1)).filter (fun i => (step^[m] 1).testBit i = true)).image
        (fun i : ℕ => (i : ℤ) - m) := by
    ext r
    simp only [window, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hr⟩
      have hp : 0 ≤ r + (m : ℤ) := by omega
      refine ⟨(r + (m : ℤ)).toNat, ⟨by omega, ?_⟩, by omega⟩
      rw [encoding_bridge g step hs m r] at hr
      simpa [bitAt, hp] using hr
    · rintro ⟨i, ⟨hi, hb⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [encoding_bridge g step hs]
      simpa [bitAt] using hb
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ) - m) := by
    intro a b h
    have he : (a : ℤ) = (b : ℤ) := sub_left_inj.mp h
    exact_mod_cast he
  rw [supportCard, hset, Set.ncard_coe_finset, hwindow,
    Finset.card_image_of_injective _ hinj]
  exact (Nat.count_eq_card_filter_range (p := fun i => (step^[m] 1).testBit i = true) _).symm

/-- The sign pattern fails at the non-Mersenne row 767, where the difference is -5. -/
theorem result : ¬ claim := by
  have bit_steps :
      (∀ b z, bitAt (step30 b) z = g30 (bitAt b (z - 2)) (bitAt b (z - 1)) (bitAt b z)) ∧
      (∀ b z, bitAt (step22 b) z = g22 (bitAt b (z - 2)) (bitAt b (z - 1)) (bitAt b z)) := by
    have shift (b a : ℕ) (z : ℤ) : bitAt (b <<< a) z = bitAt b (z - a) := by
      by_cases hz : 0 ≤ z
      · by_cases ha : (a : ℤ) ≤ z
        · have hza : 0 ≤ z - (a : ℤ) := by omega
          have hb : a ≤ z.toNat := by omega
          have hi : (z - (a : ℤ)).toNat = z.toNat - a := by omega
          simp only [bitAt, hz, hza, decide_true, Bool.true_and, Nat.testBit_shiftLeft, hb, hi]
        · have hza : ¬ 0 ≤ z - (a : ℤ) := by omega
          have hb : ¬ a ≤ z.toNat := by omega
          simp only [bitAt, hz, hza, decide_true, decide_false, Bool.true_and,
            Bool.false_and, Nat.testBit_shiftLeft, hb]
      · have hza : ¬ 0 ≤ z - (a : ℤ) := by omega
        simp only [bitAt, hz, hza, decide_false, Bool.false_and]
    have xor (a b : ℕ) (z : ℤ) : bitAt (a ^^^ b) z = (bitAt a z ^^ bitAt b z) := by
      by_cases hz : 0 ≤ z <;>
        simp only [bitAt, hz, decide_true, decide_false, Bool.true_and,
          Bool.false_and, Nat.testBit_xor, Bool.false_bne]
    have land (a b : ℕ) (z : ℤ) : bitAt (a &&& b) z = (bitAt a z && bitAt b z) := by
      by_cases hz : 0 ≤ z
      · simpa only [bitAt, hz, decide_true, Bool.true_and] using Nat.testBit_land a b z.toNat
      · simp only [bitAt, hz, decide_false, Bool.false_and]
    have lor (a b : ℕ) (z : ℤ) : bitAt (a ||| b) z = (bitAt a z || bitAt b z) := by
      by_cases hz : 0 ≤ z
      · simpa only [bitAt, hz, decide_true, Bool.true_and] using Nat.testBit_lor a b z.toNat
      · simp only [bitAt, hz, decide_false, Bool.false_and, Bool.false_or]
    constructor
    · intro b z
      simp only [step30, xor, lor, shift, g30]
      cases bitAt b (z - 2) <;> cases bitAt b (z - 1) <;> cases bitAt b z <;> rfl
    · intro b z
      simp only [step22, xor, land, shift, g22]
      rfl
  -- The kernel counts the active bits of the two exact 767-step rows.
  have count30 : Nat.count (fun i => (step30^[767] 1).testBit i = true) 1535 = 763 := by
    decide +kernel
  have count22 : Nat.count (fun i => (step22^[767] 1).testBit i = true) 1535 = 768 := by
    decide +kernel
  have eps767 : eps 767 = -5 := by
    rw [eps, support_encoded g30 step30 (by rfl) bit_steps.1,
      support_encoded g22 step22 (by rfl) bit_steps.2]
    change (Nat.count (fun i => (step30^[767] 1).testBit i = true) 1535 : ℤ) -
      (Nat.count (fun i => (step22^[767] 1).testBit i = true) 1535 : ℤ) = -5
    rw [count30, count22]
    decide
  intro hc
  obtain ⟨k, hk, he⟩ := (hc 767 (by omega)).mp (by rw [eps767]; omega)
  have hp : 2 ^ k = (768 : ℕ) := by
    have hpos : 0 < (2 : ℕ)^k := Nat.pow_pos (by omega)
    omega
  have hlow : 9 < k := by
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (show k ≤ 9 by omega)
    rw [hp] at hpow
    norm_num at hpow
    omega
  have hpow := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (show 10 ≤ k by omega)
  rw [hp] at hpow
  norm_num at hpow
  omega

end D5.S0.Automata.RuleThirtyTwentyTwoMersenneSignRefutation
