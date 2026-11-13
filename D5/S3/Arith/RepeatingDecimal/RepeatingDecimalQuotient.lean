/- GID: D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient
   generality: G
   mirror-B: D5/B/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer long division realizes rational values and prescribed periods. -/

module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Tactic

/-! Recursive integer long division and its positional real value. -/

@[expose] public section

namespace D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient

open Filter Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The integer remainder after each fractional long-division step. -/
def remainder (b p q : ℕ) : ℕ → ℕ
  | 0 => p
  | n + 1 => (b * remainder b p q n) % q

/-- The next digit is the quotient of the scaled current remainder. -/
def digit (b p q n : ℕ) : ℕ := b * remainder b p q n / q

/-- The integer represented by the first `n` fractional digits, in reading order. -/
def longDivisionPrefix (b p q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => b * longDivisionPrefix b p q n + digit b p q n

/-- Long division conserves the original scaled numerator at every prefix length. -/
theorem long_division_invariant (b p q n : ℕ) :
    q * longDivisionPrefix b p q n + remainder b p q n = b ^ n * p := by
  induction n with
  | zero => simp [longDivisionPrefix, remainder]
  | succ n ih =>
    calc
      q * longDivisionPrefix b p q (n + 1) + remainder b p q (n + 1) =
          b * (q * longDivisionPrefix b p q n) +
            (q * (b * remainder b p q n / q) + b * remainder b p q n % q) := by
        simp only [longDivisionPrefix, remainder, digit]
        ring
      _ = b * (q * longDivisionPrefix b p q n) + b * remainder b p q n := by
        rw [Nat.div_add_mod]
      _ = b * (q * longDivisionPrefix b p q n + remainder b p q n) := by ring
      _ = b ^ (n + 1) * p := by rw [ih, pow_succ]; ring

private theorem remainder_lt {b p q : ℕ} (hp : p < q) (n : ℕ) :
    remainder b p q n < q := by
  cases n with
  | zero => exact hp
  | succ n => exact Nat.mod_lt _ (Nat.zero_lt_of_lt hp)

private theorem digit_lt {b p q : ℕ} (hb : 0 < b) (hp : p < q) (n : ℕ) :
    digit b p q n < b := by
  rw [digit, Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hp)]
  simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left (remainder_lt hp n) hb

private theorem prefix_sum {b : ℕ} (hb : 0 < b) (p q n : ℕ) :
    (longDivisionPrefix b p q n : ℝ) / (b : ℝ) ^ n =
      ∑ i ∈ Finset.range n, (digit b p q i : ℝ) / (b : ℝ) ^ (i + 1) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  induction n with
  | zero => simp [longDivisionPrefix]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, longDivisionPrefix, Nat.cast_add, Nat.cast_mul, pow_succ]
    field_simp

private theorem normalized_remainder {b p q : ℕ} (hb : 0 < b) (hp : p < q) (n : ℕ) :
    (longDivisionPrefix b p q n : ℝ) / (b : ℝ) ^ n +
      (remainder b p q n : ℝ) / ((q : ℝ) * (b : ℝ) ^ n) = (p : ℝ) / q := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hp)
  have hi : (q : ℝ) * longDivisionPrefix b p q n + remainder b p q n = (b : ℝ) ^ n * p := by
    exact_mod_cast long_division_invariant b p q n
  field_simp
  nlinarith [hi]

/-- The actual long-division digits form a convergent positional series for `p/q`;
the same value is the limit of the normalized integer prefixes. -/
theorem long_division_value {b p q : ℕ} (hb : 1 < b) (hp : p < q) :
    HasSum (fun n => (digit b p q n : ℝ) / (b : ℝ) ^ (n + 1)) ((p : ℝ) / q) ∧
      Tendsto (fun n => (longDivisionPrefix b p q n : ℝ) / (b : ℝ) ^ n)
        atTop (𝓝 ((p : ℝ) / q)) := by
  have hbpos : 0 < b := Nat.zero_lt_of_lt hb
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hrem : Tendsto (fun n =>
      (remainder b p q n : ℝ) / ((q : ℝ) * (b : ℝ) ^ n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hbR))
    calc
      (remainder b p q n : ℝ) / ((q : ℝ) * (b : ℝ) ^ n) ≤
          (q : ℝ) / ((q : ℝ) * (b : ℝ) ^ n) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (remainder_lt hp n).le
      _ = ((b : ℝ)⁻¹) ^ n := by rw [inv_pow]; field_simp
  have hlimit : Tendsto (fun n => (longDivisionPrefix b p q n : ℝ) / (b : ℝ) ^ n)
      atTop (𝓝 ((p : ℝ) / q)) := by
    have h := (tendsto_const_nhds (x := (p : ℝ) / q)).sub hrem
    simp only [sub_zero] at h
    apply h.congr
    intro n
    linarith [normalized_remainder hbpos hp n]
  have hsummable : Summable (fun n => (digit b p q n : ℝ) / (b : ℝ) ^ (n + 1)) := by
    let a : ℕ → Fin b := fun n => ⟨digit b p q n, digit_lt hbpos hp n⟩
    change Summable (Real.ofDigitsTerm a)
    exact Real.summable_ofDigitsTerm
  refine ⟨?_, hlimit⟩
  apply (hasSum_iff_tendsto_nat_of_summable_norm (show Summable (fun n =>
    ‖(digit b p q n : ℝ) / (b : ℝ) ^ (n + 1)‖) from
      hsummable.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm))).mpr
  exact hlimit.congr (fun n => prefix_sum hbpos p q n)

/-- A divisor of the period kernel gives a pure digit period and the corresponding
shift/quotient identity for the integer block produced by long division. -/
theorem long_division_period {b p q : ℕ} (hb : 1 < b) (hp : p < q)
    (L : ℕ) (hL : q ∣ b ^ L - 1) :
    Function.Periodic (digit b p q) L ∧
      ((b : ℝ) ^ L - 1) * ((p : ℝ) / q) = (longDivisionPrefix b p q L : ℝ) := by
  obtain ⟨k, hk⟩ := hL
  have hpow : b ^ L = 1 + q * k := by
    have := Nat.one_le_pow L b (by omega)
    omega
  have hreturn : remainder b p q L = p := by
    have hi := congrArg (fun x : ℕ => x % q) (long_division_invariant b p q L)
    have hmod : (b ^ L * p) % q = p := by
      calc
        (b ^ L * p) % q = (p + q * (k * p)) % q := by rw [hpow]; congr 1; ring
        _ = p := by simp [Nat.mod_eq_of_lt hp]
    simpa [Nat.add_mod, hmod, Nat.mod_eq_of_lt (remainder_lt hp L)] using hi
  have hshift : ∀ n, remainder b p q (n + L) = remainder b p q n := by
    intro n
    induction n with
    | zero => simpa [remainder] using hreturn
    | succ n ih =>
      rw [show n + 1 + L = (n + L) + 1 by omega, remainder, remainder, ih]
  refine ⟨fun n => by simp only [digit, hshift], ?_⟩
  have hi : (q : ℝ) * longDivisionPrefix b p q L + p = (b : ℝ) ^ L * p := by
    have hi := long_division_invariant b p q L
    rw [hreturn] at hi
    exact_mod_cast hi
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hp)
  field_simp
  nlinarith [hi]

#print axioms long_division_invariant
#print axioms long_division_value
#print axioms long_division_period

end D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
