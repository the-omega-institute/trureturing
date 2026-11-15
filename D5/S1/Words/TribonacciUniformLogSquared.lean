/- GID: D5/S1/Words/TribonacciUniformLogSquared
   generality: I
   mirror-B: D5/B/S1/Words/TribonacciUniformLogSquared
   mirror-E: none(waiver:literal-word-analysis)
   anchors: []
   utility: none
   digest: A squared logarithm bounds all alternating intervals of the literal Tribonacci word. -/
import D5.S1.Words.SubstitutionPrefixEnvelope
import D5.S1.Words.TribonacciPrefixRefutation
import D5.S1.Words.MBonacciFactorWindow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Log

/-! Uniform interval estimates for the literal Tribonacci word. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TribonacciUniformLogSquared

open RankOneMorphismIterationBound (subst image image_add)
open TribonacciPrefixRefutation (Letter tau weight signedWordSum)
open TribonacciAlignedWindows (sigma W)
open AbelianBorders.AbelianBorderQuestionDefs (factor)
open SubstitutionPrefixEnvelope (charge)
open scoped BigOperators

private theorem image_tau (j : ℕ) (a : Letter) : image tau j a = image sigma (4*j) a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change subst (image sigma 4) (image tau j a) = _
    rw [ih, ← image_add]
    congr 1
    omega

private theorem tau_lengths (a : Letter) : 7 ≤ (tau a).length ∧ (tau a).length ≤ 13 := by
  fin_cases a
  · change 7 ≤ (tau 0).length ∧ (tau 0).length ≤ 13
    rw [TribonacciPrefixRefutation.tau_A]; decide
  · change 7 ≤ (tau 1).length ∧ (tau 1).length ≤ 13
    rw [TribonacciPrefixRefutation.tau_B]; decide
  · change 7 ≤ (tau 2).length ∧ (tau 2).length ≤ 13
    rw [TribonacciPrefixRefutation.tau_C]; decide

private theorem block_charge (j : ℕ) (a : Letter) :
    |charge weight (image tau j a)| ≤ 2*(j : ℤ)+4 := by
  rw [image_tau]
  change |signedWordSum (image sigma (4*j) a)| ≤ _
  obtain ⟨ha, hb, hc⟩ := TribonacciPrefixRefutation.abc_closed j
  have hs : |(-1 : ℤ)^j| = 1 := abs_neg_one_pow j
  have hj : 0 ≤ (j : ℤ) := by positivity
  fin_cases a
  · change |TribonacciPrefixRefutation.a j| ≤ _
    rw [ha]; norm_num; omega
  · change |TribonacciPrefixRefutation.b j| ≤ _
    rw [hb]
    have h := abs_sub (2 : ℤ) ((-1 : ℤ)^j)
    norm_num [hs] at h
    omega
  · change |TribonacciPrefixRefutation.c j| ≤ _
    rw [hc]
    have h := abs_sub (2 : ℤ) ((2*(j : ℤ)+2)*(-1 : ℤ)^j)
    rw [abs_mul, hs, mul_one] at h
    rw [abs_of_nonneg (by omega : 0 ≤ 2*(j : ℤ)+2)] at h
    norm_num at h
    omega

private theorem iterate_length_lower (j : ℕ) (a : Letter) :
    7^j ≤ (image tau j a).length := by
  induction j generalizing a with
  | zero => simp [image]
  | succ j ih =>
    have h (v : List Letter) : 7^j * v.length ≤ (v.flatMap (image tau j)).length := by
      induction v with
      | nil => simp
      | cons x v ihv =>
        have hx := ih x
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        nlinarith
    have hh := h (tau a)
    have ha := (tau_lengths a).1
    have he : image tau (j+1) a = (tau a).flatMap (image tau j) := by
      rw [image_add tau j 1]
      simp only [image, subst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [he]
    rw [pow_succ]
    nlinarith

private theorem envelope_polynomial (j : ℕ) :
    (2 : ℤ) + 13 * ∑ i ∈ Finset.range j, (2*(i : ℤ)+4) =
      2 + 13*(j : ℤ)^2 + 39*(j : ℤ) := by
  have hs : (∑ i ∈ Finset.range j, (i : ℤ)) * 2 =
      (j : ℤ) * ((j-1 : ℕ) : ℤ) := by
    have hh := congrArg (fun n : ℕ => (n : ℤ)) (Finset.sum_range_id_mul_two j)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using hh
  by_cases hj : j = 0
  · subst j; simp
  rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one] at hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith

private theorem interval_level_bound (j : ℕ) (x y : Letter) (v : List Letter)
    (hv : v <:+: image tau j x ++ image tau j y) :
    |signedWordSum v| ≤ 156 * ((j : ℤ)+1)^2 := by
  have hw : ∀ x : Letter, |weight x| ≤ 2 := by
    intro x; fin_cases x <;> norm_num [weight]
  have hh := SubstitutionPrefixEnvelope.two_block_interval_bound weight tau 2 13
    (fun i => 2*(i : ℤ)+4) (by norm_num) hw (fun x => (tau_lengths x).2)
    (by intro i; positivity) block_charge j x y v hv
  norm_num only [Nat.cast_ofNat] at hh
  rw [envelope_polynomial] at hh
  change |signedWordSum v| ≤ _ at hh
  have hj : 0 ≤ (j : ℤ) := by positivity
  nlinarith [sq_nonneg (j : ℤ)]

private theorem actual_interval_bound (s m j : ℕ) (hm : 0 < m) (hj : m < 7 ^ j) :
    |signedWordSum (factor W s m)| ≤ 156 * ((j : ℤ)+1)^2 := by
  let N := j + s + m
  have hNj : j ≤ N := by dsimp [N]; omega
  have hlen : s + m ≤ (image sigma (4*N) 0).length := by
    have hh := MBonacciSentinelDesubstitution.iterate_growth (by omega : 2 ≤ 3) (4*N)
    change 4*N+1 ≤ (image sigma (4*N) 0).length at hh
    dsimp [N] at *
    omega
  have he := MBonacciFactorWindow.factor_eq_take_drop (by omega : 2 ≤ 3) (4*N) s m hlen
  change factor W s m = ((image sigma (4*N) 0).drop s).take m at he
  rw [← image_tau] at he hlen
  have hsplit : image tau N 0 = (image tau (N-j) 0).flatMap (image tau j) := by
    have heq : N = j + (N-j) := by omega
    conv_lhs => rw [heq, image_add]
    rfl
  rw [hsplit] at he hlen
  have hblocks : ∀ a ∈ image tau (N-j) 0, m < (image tau j a).length := by
    intro a _
    exact hj.trans_le (iterate_length_lower j a)
  obtain (⟨a, _, ha⟩ | ⟨a, b, _, hab⟩) :=
    flatMap_window_infix_one_or_two hm hblocks hlen
  · rw [he]
    apply interval_level_bound j a a
    exact ha.trans List.infix_append_left
  · rw [he]
    exact interval_level_bound j a b _ hab

/-- One constant controls every start and every length, with a local positive
first sign, for the literal A-starting Tribonacci word and weights 2, 1, 0. -/
theorem uniform_log_squared : ∃ C : ℝ, 0 < C ∧ ∀ s m : ℕ,
    |(signedWordSum (factor W s m) : ℝ)| ≤ C * (Real.log (m+2))^2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1404 / (Real.log 2)^2, by positivity, ?_⟩
  intro s m
  by_cases hm : m = 0
  · subst m
    simp [factor, signedWordSum]
    positivity
  have hmp : 0 < m := by omega
  let k := Nat.log 7 m
  let j := k+1
  have hj : m < 7^j := Nat.lt_pow_succ_log_self (by norm_num : 1 < 7) m
  have hh := actual_interval_bound s m j hmp hj
  have hhR : |(signedWordSum (factor W s m) : ℝ)| ≤ 156*((j : ℝ)+1)^2 := by
    exact_mod_cast hh
  have hpow : 2^k ≤ m :=
    (Nat.pow_le_pow_left (by norm_num : 2 ≤ 7) k).trans (Nat.pow_log_le_self 7 hm)
  have hpowR : (2 : ℝ)^k ≤ (m : ℝ)+2 := by exact_mod_cast (show 2^k ≤ m+2 by omega)
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2^k) hpowR
  rw [Real.log_pow] at hl
  have hl₂ : Real.log 2 ≤ Real.log ((m : ℝ)+2) :=
    Real.log_le_log (by norm_num) (by
      have : (0 : ℝ) ≤ m := by positivity
      linarith)
  have hjlog : ((j : ℝ)+1) * Real.log 2 ≤ 3*Real.log ((m : ℝ)+2) := by
    dsimp [j]
    push_cast
    linarith
  have hjbound : (j : ℝ)+1 ≤ 3*Real.log ((m : ℝ)+2) / Real.log 2 :=
    (le_div_iff₀ hlog).2 hjlog
  have hL : 0 ≤ Real.log ((m : ℝ)+2) := le_trans (le_of_lt hlog) hl₂
  have hsquare := sq_le_sq₀ (by positivity : 0 ≤ (j : ℝ)+1)
    (by positivity : 0 ≤ 3*Real.log ((m : ℝ)+2) / Real.log 2)
  have hs : ((j : ℝ)+1)^2 ≤ (3*Real.log ((m : ℝ)+2) / Real.log 2)^2 :=
    hsquare.2 hjbound
  calc
    |(signedWordSum (factor W s m) : ℝ)| ≤ 156*((j : ℝ)+1)^2 := hhR
    _ ≤ 156*(3*Real.log ((m : ℝ)+2) / Real.log 2)^2 := by nlinarith
    _ = (1404 / (Real.log 2)^2) * (Real.log ((m : ℝ)+2))^2 := by ring

end D5.S1.Words.TribonacciUniformLogSquared
