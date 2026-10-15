/- GID: D5/S3/Arith/Additive/FibonacciSuperAccessibility
   generality: I
   mirror-B: D5/B/S3/Arith/Additive/FibonacciSuperAccessibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Additive/FibonacciSuperAccessibility.claim; result=D5/S3/Arith/Additive/FibonacciSuperAccessibility.result; claim=D5/S3/Arith/Additive/FibonacciSuperAccessibility.claim
   digest: Fibonacci rotation coloring refutes 2-super-accessibility. -/

/-
proof_shape: fibSet, HasAP, HasDiffSeq, SuperAccessible, claim, coloring: definitions
proof_shape: no_color_one_ap: content; consumer: result
proof_shape: no_color_two_diffseq: content; consumer: result
proof_shape: result: content (explicit rotation-coloring refutation assembled from the definitions and pinned Mathlib arithmetic)
proof_shape: coloring_range: bind-only; consumer: result
proof_shape: alpha_fib: bind-only; consumer: phase_fib
proof_shape: residue_rec: bind-only; consumer: residue_block
proof_shape: block_rec: bind-only; consumer: residue_block
proof_shape: residue_block: content; consumers: residue_bounds, residue_coprime
proof_shape: residue_bounds: content; consumers: phase_fib, phase_fib_bounds
proof_shape: psi_abs_lt: bind-only; consumer: psi_pow_small
proof_shape: psi_pow_small: bind-only; consumers: phase_fib, phase_fib_bounds, large_gap_hit
proof_shape: phase_fib: content; consumer: phase_fib_bounds
proof_shape: phase_fib_bounds: content; consumer: color_two_step
proof_shape: fract_no_wrap: bind-only; consumer: color_two_step
proof_shape: color_two_iff: bind-only; consumers: color_two_step, no_color_two_diffseq, no_color_one_ap
proof_shape: color_two_step: content; consumer: no_color_two_diffseq
proof_shape: uniform_hitting: content; consumers: large_gap_hit, rational_certificate_hit
proof_shape: residue_coprime: content; consumer: large_gap_hit
proof_shape: large_gap_hit: content; consumer: fib_gap_hit
proof_shape: alpha_bracket: bind-only; consumer: rational_certificate_hit
proof_shape: rational_certificate_hit: content; consumer: small_gap_hit
proof_shape: small_gap_hit: content; consumer: fib_gap_hit
proof_shape: fib_gap_hit: content; consumer: no_color_one_ap
escape_witness: no_color_one_ap: no_color_one_ap (uniform Fibonacci-gap hitting)
escape_witness: no_color_two_diffseq: no_color_two_diffseq (two strict phase advances)
escape_witness: result: no_color_one_ap and no_color_two_diffseq
admission_basis: open-problem-resolution (#16039; Refuted)
escape_audit: unfinished for no_color_one_ap, no_color_two_diffseq, and the published
GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap; issue #16300.
The designated refutation result (basis=refutes) is exempt from four-slot escape registration.
Direct frozen dependencies:
  D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap
  statement_id sha256:9e01d89531197864aad08bff684b75f8ad15d1688b41c1246f0c4094c0ebfda9
  D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.forwardDisplacement
  statement_id sha256:15bcb39d2cb2866665c4cb1f37f064fe7e07b50130bb5b90c00c9ae28e863171
  D5/S1/Phase/ThreeGap/Returns.fract_add_fract_eq
  statement_id sha256:bea4f8feec65daf1fdc9d991cbefb91ff9b903f2837199e6e363f6cd3b467c15
The public claim keeps the preregistered literal definitions; alpha is private, and the frozen forwardDisplacement owner supplies the phase expression inside the consuming proof.
The residue block is indexed by n % 7 starting at n = 0.
-/

import D5.S1.Words.ReturnWords.GoldenArcFirstReturnCore
import D5.S1.Phase.ThreeGap.Returns
namespace D5.S3.Arith.Additive.FibonacciSuperAccessibility
open D5.S1.Words.GoldenArcFirstReturnInternal
noncomputable section

def fibSet : Set ℕ := {d | ∃ n, 1 ≤ n ∧ d = Nat.fib n}
def HasAP (S A : Set ℕ) (k : ℕ) : Prop := ∃ x d, 1 ≤ x ∧ d ∈ S ∧ ∀ i < k, x + i * d ∈ A
def HasDiffSeq (S A : Set ℕ) (k : ℕ) : Prop :=
  ∃ x : ℕ → ℕ, 1 ≤ x 0 ∧
    (∀ i, i + 1 < k → x i < x (i + 1) ∧ x (i + 1) - x i ∈ S) ∧ ∀ i < k, x i ∈ A
def SuperAccessible (r : ℕ) (S : Set ℕ) : Prop :=
  ∀ c : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ c n ∧ c n ≤ r) →
    (∀ k, HasAP S {n | c n = 1} k) ∨
      ∃ j, 2 ≤ j ∧ j ≤ r ∧ ∀ k, HasDiffSeq S {n | c n = j} k
def claim : Prop := SuperAccessible 2 fibSet

private def alpha : ℝ := (47 + Real.sqrt 5) / 58
def coloring (n : ℕ) : ℕ :=
  if Int.fract (((47 + Real.sqrt 5) / 58) * n) < 1 / 16 then 2 else 1

private theorem coloring_range (n : ℕ) : 1 ≤ coloring n ∧ coloring n ≤ 2 := by
  unfold coloring
  split_ifs <;> norm_num

private theorem alpha_fib (n : ℕ) :
    29 * alpha * Nat.fib n = (23 * Nat.fib n + Nat.fib (n + 1) : ℕ) - Real.goldenConj ^ n := by
  have h := Real.fib_succ_sub_goldenRatio_mul_fib n
  push_cast
  dsimp [alpha, Real.goldenRatio] at *
  nlinarith

private def residue (n : ℕ) : ℕ := (23 * Nat.fib n + Nat.fib (n + 1)) % 29
private def block (n : ℕ) : ℕ := match n % 7 with
  | 0 => 1 | 1 => 24 | 2 => 25 | 3 => 20 | 4 => 16 | 5 => 7 | _ => 23

private theorem residue_rec (n : ℕ) : residue (n + 2) = (residue n + residue (n + 1)) % 29 := by
  simp only [residue, Nat.fib_add_two]
  omega

private theorem block_rec (n : ℕ) : block (n + 2) = (block n + block (n + 1)) % 29 := by
  have h := Nat.mod_lt n (by omega : 0 < 7)
  interval_cases e : n % 7 <;> norm_num [block, Nat.add_mod, e]

private theorem residue_block (n : ℕ) : residue n = block n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [residue, block]
  | one => norm_num [residue, block]
  | more n ih0 ih1 => rw [residue_rec, ih0, ih1, ← block_rec]

private theorem residue_bounds (n : ℕ) :
    1 ≤ residue n ∧ residue n ≤ 25 ∧ (residue n = 1 → n % 7 = 0) ∧
    (residue n ≠ 1 → 7 ≤ residue n) := by
  rw [residue_block]
  have h := Nat.mod_lt n (by omega : 0 < 7)
  interval_cases e : n % 7 <;> norm_num [block, e]

private theorem psi_abs_lt : |Real.goldenConj| < 5/8 := by
  rw [abs_of_neg Real.goldenConj_neg]
  dsimp [Real.goldenConj]
  have h : Real.sqrt 5 < 9/4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

private theorem psi_pow_small (n k : ℕ) (hk : k ≤ n) :
    |Real.goldenConj ^ n| ≤ (5/8 : ℝ)^k := by
  rw [abs_pow]
  calc
    |Real.goldenConj|^n ≤ (5/8 : ℝ)^n := pow_le_pow_left₀ (abs_nonneg _) psi_abs_lt.le _
    _ ≤ (5/8 : ℝ)^k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk

private theorem phase_fib (n : ℕ) (hn : 1 ≤ n) :
    forwardDisplacement alpha (Nat.fib n) = ((residue n : ℝ) - Real.goldenConj ^ n) / 29 := by
  have hr := residue_bounds n
  have hb := psi_pow_small n 1 hn
  have hp := (abs_le.mp hb)
  apply Int.fract_eq_iff.mpr
  refine ⟨by norm_num at hb; nlinarith [show (1 : ℝ) ≤ residue n by exact_mod_cast hr.1],
    by norm_num at hb; nlinarith [show (residue n : ℝ) ≤ 25 by exact_mod_cast hr.2.1],
    ((23 * Nat.fib n + Nat.fib (n + 1)) / 29 : ℕ), ?_⟩
  have hd := Nat.mod_add_div (23 * Nat.fib n + Nat.fib (n + 1)) 29
  have hdc : (residue n : ℝ) + 29 * (((23 * Nat.fib n + Nat.fib (n + 1)) / 29 : ℕ) : ℝ) =
      (23 * Nat.fib n + Nat.fib (n + 1) : ℕ) := by exact_mod_cast hd
  have hf := alpha_fib n
  simp only [Int.cast_natCast]
  nlinarith

private theorem phase_fib_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 / 32 : ℝ) < forwardDisplacement alpha (Nat.fib n) ∧ forwardDisplacement alpha (Nat.fib n) < 26 / 29 := by
  rw [phase_fib n hn]
  have hr := residue_bounds n
  have h1 : (1 : ℝ) ≤ residue n := by exact_mod_cast hr.1
  have h25 : (residue n : ℝ) ≤ 25 := by exact_mod_cast hr.2.1
  have hb := abs_le.mp (psi_pow_small n 1 hn)
  constructor
  · by_cases he : residue n = 1
    · have hn7 : 7 ≤ n := by have := hr.2.2.1 he; omega
      have hs := abs_le.mp (psi_pow_small n 7 hn7)
      norm_num at hs
      rw [he]; norm_num; linarith
    · have h7 : (7 : ℝ) ≤ residue n := by exact_mod_cast hr.2.2.2 he
      norm_num at hb
      linarith
  · norm_num at hb
    linarith

private theorem fract_no_wrap (a b : ℝ) (h : Int.fract a + Int.fract b < 1) :
    Int.fract (a+b) = Int.fract a + Int.fract b := by
  have ho := fract_add_displacement_of_no_wrap (alpha := Int.fract b) (x := Int.fract a) 1 (Int.fract_nonneg a) (by simpa [forwardDisplacement] using h)
  simpa only [Nat.cast_one, one_mul, forwardDisplacement, Int.fract_fract, ThreeGap.fract_add_fract_eq] using ho

private theorem color_two_iff (n : ℕ) : coloring n = 2 ↔ forwardDisplacement alpha n < 1 / 16 := by
  simp [coloring, forwardDisplacement, alpha, mul_comm]

private theorem color_two_step (x d : ℕ) (hd : d ∈ fibSet) (hx : coloring x = 2) :
    forwardDisplacement alpha x + 1 / 32 < forwardDisplacement alpha (x + d) := by
  rcases hd with ⟨n, hn, rfl⟩
  have hb := phase_fib_bounds n hn
  have hx' := (color_two_iff x).mp hx
  have he : forwardDisplacement alpha (x + Nat.fib n) = forwardDisplacement alpha x + forwardDisplacement alpha (Nat.fib n) := by
    simp only [forwardDisplacement, mul_comm]
    rw [Nat.cast_add, mul_add]
    apply fract_no_wrap
    have hsum : forwardDisplacement alpha x + forwardDisplacement alpha (Nat.fib n) < 1 := by linarith
    simpa only [forwardDisplacement, mul_comm] using hsum
  rw [he]
  linarith

theorem no_color_two_diffseq : ¬ HasDiffSeq fibSet {n | coloring n = 2} 3 := by
  rintro ⟨x, hx, hs, hc⟩
  have h0 := hs 0 (by omega)
  have h1 := hs 1 (by omega)
  norm_num at h0 h1
  have c0 : coloring (x 0) = 2 := hc 0 (by omega)
  have c2 : coloring (x 2) = 2 := hc 2 (by omega)
  have t0 := color_two_step (x 0) (x 1 - x 0) h0.2 c0
  have t1 := color_two_step (x 1) (x 2 - x 1) h1.2 (hc 1 (by omega))
  have e0 : x 0 + (x 1 - x 0) = x 1 := by omega
  have e1 : x 1 + (x 2 - x 1) = x 2 := by omega
  rw [e0] at t0
  rw [e1] at t1
  have hn : 0 ≤ forwardDisplacement alpha (x 0) := Int.fract_nonneg _
  have ht := (color_two_iff (x 2)).mp c2
  linarith

private theorem uniform_hitting (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime p (q : ℤ)) (eps w t : ℝ) (hw : w < 1)
    (hwidth : 1 / (q : ℝ) + ((q : ℝ) - 1) * |eps| < w) :
    ∃ j : ℕ, j < q ∧ Int.fract (t + j * ((p : ℝ)/q + eps)) < w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) ≤ (q : ℝ)-1 := by
    have h' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  let m := min 0 (((q : ℝ) - 1) * eps)
  let theta := Int.fract (t+m)
  let h : ℤ := ⌊(q : ℝ)*theta⌋
  let : NeZero q := ⟨by omega⟩
  let j : ℕ := (-(h : ZMod q) * (p : ZMod q)⁻¹).val
  have hj : j < q := ZMod.val_lt _
  have hjR : (j : ℝ) ≤ (q : ℝ)-1 := by
    have h' : (j : ℝ)+1 ≤ q := by exact_mod_cast hj
    linarith
  have hz : ((h + (j : ℤ)*p : ℤ) : ZMod q) = 0 := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    dsimp [j]
    rw [ZMod.natCast_zmod_val, mul_assoc, ZMod.coe_int_inv_mul_eq_one hcop]
    simp
  obtain ⟨l, hl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (h+(j : ℤ)*p) q).mp hz
  have hlR : (h : ℝ) + (j : ℝ)*(p : ℝ) = (q : ℝ)*(l : ℝ) := by exact_mod_cast hl
  let v := theta - (h : ℝ)/q
  have hv0 : 0 ≤ v := by
    have hf := Int.floor_le ((q : ℝ)*theta)
    change (h : ℝ) ≤ (q : ℝ)*theta at hf
    dsimp [v]
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hqR).mpr (by nlinarith [hf])
  have hv1 : v < 1 / (q : ℝ) := by
    have hf := Int.lt_floor_add_one ((q : ℝ)*theta)
    change (q : ℝ)*theta < (h : ℝ)+1 at hf
    dsimp [v]
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hqR]
    nlinarith [hf]
  have heps : 0 ≤ (j : ℝ)*eps-m ∧ (j : ℝ)*eps-m ≤ ((q : ℝ) - 1) * |eps| := by
    by_cases he : 0 ≤ eps
    · have hm : m = 0 := min_eq_left (mul_nonneg hq1 he)
      rw [hm, abs_of_nonneg he]
      constructor
      · simpa using mul_nonneg (Nat.cast_nonneg j) he
      · nlinarith [mul_le_mul_of_nonneg_right hjR he]
    · have hm : m = ((q : ℝ) - 1) * eps := min_eq_right (mul_nonpos_of_nonneg_of_nonpos hq1 (le_of_not_ge he))
      rw [hm, abs_of_neg (lt_of_not_ge he)]
      constructor <;> nlinarith [mul_le_mul_of_nonpos_right hjR (le_of_not_ge he),
        mul_nonpos_of_nonneg_of_nonpos (show (0 : ℝ) ≤ j by positivity) (le_of_not_ge he)]
  have hve0 : 0 ≤ v+(j : ℝ)*eps-m := by linarith
  have hvew : v+(j : ℝ)*eps-m < w := by linarith
  have ht : Int.fract (t + j * ((p : ℝ)/q + eps)) = v+(j : ℝ)*eps-m := by
    apply Int.fract_eq_iff.mpr
    refine ⟨hve0, lt_trans hvew hw, ⌊t+m⌋ + l, ?_⟩
    have htheta := Int.floor_add_fract (t+m)
    change (⌊t+m⌋ : ℝ) + theta = t+m at htheta
    simp only [Int.cast_add]
    dsimp [v]
    field_simp
    nlinarith
  exact ⟨j, hj, ht ▸ hvew⟩

private theorem residue_coprime (n : ℕ) : Nat.Coprime (residue n) 29 := by
  rw [residue_block]
  have h := Nat.mod_lt n (by omega : 0 < 7)
  interval_cases e : n % 7 <;> norm_num [block, e]

private theorem large_gap_hit (n : ℕ) (hn : 8 ≤ n) (t : ℝ) :
    ∃ j : ℕ, j < 29 ∧ Int.fract (t+j*(alpha*Nat.fib n)) < 1 / 16 := by
  let a := 23 * Nat.fib n + Nat.fib (n + 1)
  have hcop : Nat.Coprime a 29 := by
    apply (ZMod.coprime_mod_iff_coprime a 29).mp
    exact residue_coprime n
  have he : |-(Real.goldenConj ^ n)/29| < (1/(29*40) : ℝ) := by
    rw [abs_div, abs_neg]
    norm_num
    have h := psi_pow_small n 8 hn
    norm_num at h
    linarith
  have hw : 1/(29 : ℝ) + ((29 : ℝ)-1)*|-(Real.goldenConj ^ n)/29| < 1 / 16 := by
    norm_num
    linarith
  have hd : (a : ℝ)/29 + (-(Real.goldenConj ^ n)/29) = alpha*Nat.fib n := by
    have h := alpha_fib n
    change 29*alpha*Nat.fib n = (a : ℝ)-Real.goldenConj^n at h
    linarith
  obtain ⟨j, hj, hh⟩ := uniform_hitting (a : ℤ) 29 (by norm_num) hcop.isCoprime
    (-(Real.goldenConj ^ n)/29) (1 / 16) t (by norm_num) hw
  norm_num only [Nat.cast_ofNat, Int.cast_natCast] at hh
  rw [hd] at hh
  exact ⟨j, hj, hh⟩

private theorem alpha_bracket :
    (848897/1000000 : ℝ) < alpha ∧ alpha < 848898/1000000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  dsimp [alpha]
  constructor <;> nlinarith

private theorem rational_certificate_hit (d p q : ℕ) (E : ℝ) (hq : 0 < q) (hq42 : q ≤ 42)
    (hcop : Nat.Coprime p q)
    (hlo : -E ≤ (d : ℝ) * (848897 / 1000000) - (p : ℝ) / q)
    (hhi : (d : ℝ) * (848898 / 1000000) - (p : ℝ) / q ≤ E)
    (hw : 1 / (q : ℝ)+((q : ℝ) - 1) * E < 1 / 16) (t : ℝ) :
    ∃ j : ℕ, j < 42 ∧ Int.fract (t+j*(alpha*d)) < 1 / 16 := by
  have hab := alpha_bracket
  have he : |alpha*d-(p : ℝ)/q| ≤ E := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hab.1.le),
      mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hab.2.le)]
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hw' : 1 / (q : ℝ)+((q : ℝ) - 1) * |alpha*d-(p : ℝ)/q| < 1 / 16 := by
    nlinarith
  obtain ⟨j, hj, hh⟩ := uniform_hitting (p : ℤ) q hq hcop.isCoprime
    (alpha*d-(p : ℝ)/q) (1 / 16) t (by norm_num) hw'
  simp only [Int.cast_natCast] at hh
  have heq : (p : ℝ)/q + (alpha*d-(p : ℝ)/q) = alpha*d := by ring
  rw [heq] at hh
  exact ⟨j, lt_of_lt_of_le hj hq42, hh⟩

private theorem small_gap_hit (d : ℕ)
    (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 8 ∨ d = 13) (t : ℝ) :
    ∃ j : ℕ, j < 42 ∧ Int.fract (t+j*(alpha*d)) < 1 / 16 := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · apply rational_certificate_hit 1 28 33 (6817/16500000) (t := t) <;> norm_num
  · apply rational_certificate_hit 2 56 33 (6817/8250000) (t := t) <;> norm_num
  · apply rational_certificate_hit 3 107 42 (19489/21000000) (t := t) <;> norm_num
  · apply rational_certificate_hit 5 174 41 (2409/4100000) (t := t) <;> norm_num
  · apply rational_certificate_hit 8 163 24 (23/46875) (t := t) <;> norm_num
  · apply rational_certificate_hit 13 309 28 (373/7000000) (t := t) <;> norm_num

private theorem fib_gap_hit (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ∃ j : ℕ, j < 42 ∧ Int.fract (t+j*(alpha*Nat.fib n)) < 1 / 16 := by
  by_cases hlarge : 8 ≤ n
  · obtain ⟨j, hj, hh⟩ := large_gap_hit n hlarge t
    exact ⟨j, by omega, hh⟩
  · have hsmall : Nat.fib n = 1 ∨ Nat.fib n = 2 ∨ Nat.fib n = 3 ∨ Nat.fib n = 5 ∨
        Nat.fib n = 8 ∨ Nat.fib n = 13 := by
      interval_cases n <;> norm_num
    exact small_gap_hit (Nat.fib n) hsmall t

theorem no_color_one_ap : ¬ HasAP fibSet {n | coloring n = 1} 42 := by
  rintro ⟨x, d, hx, hd, hc⟩
  rcases hd with ⟨n, hn, rfl⟩
  obtain ⟨j, hj, hh⟩ := fib_gap_hit n hn (alpha*x)
  have he : forwardDisplacement alpha (x+j*Nat.fib n) = Int.fract (alpha*x+j*(alpha*Nat.fib n)) := by
    simp only [forwardDisplacement, mul_comm]
    congr 1
    push_cast
    ring
  have hcj : coloring (x+j*Nat.fib n) = 1 := hc j hj
  have htwo : coloring (x+j*Nat.fib n) = 2 := (color_two_iff _).mpr (he.symm ▸ hh)
  omega

theorem result : ¬ claim := by
  intro h
  rcases h coloring (fun n _ => coloring_range n) with hAP | ⟨j, hj0, hj2, hDS⟩
  · exact no_color_one_ap (hAP 42)
  · have hj : j = 2 := by omega
    subst j
    exact no_color_two_diffseq (hDS 3)

end
end D5.S3.Arith.Additive.FibonacciSuperAccessibility
