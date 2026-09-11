import Mathlib

/- Conditional A110037 derivation from explicit paper parity inputs.
The concrete-count premise remains open; this report artifact is not deposited. -/
namespace A110037Attempt2

/-- A distinct partition is represented by its finite set of positive parts.
For each part p, the sum of all smaller parts is its suffix sum in descending order. -/
def nonsquashingDistinctPartitions (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powerset).filter fun s =>
    s.sum id = n ∧ ∀ p ∈ s, (s.filter (fun q => q < p)).sum id ≤ p

/-- A073089's independent branch recurrence; zero is only a totalization outside its offset. -/
def paperfoldVariant (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else if n % 4 = 0 then 1
  else if n % 4 = 2 then 0
  else if n % 8 = 3 then 1
  else if n % 8 = 7 then 0
  else if n % 16 = 5 then 1
  else if n % 16 = 13 then 0
  else paperfoldVariant ((n + 1) / 2)
termination_by n

private theorem c_four (r : ℕ) (hr : 0 < r) : paperfoldVariant (4 * r) = 1 := by
  rw [paperfoldVariant]
  split_ifs <;> omega

private theorem c_four_two (r : ℕ) : paperfoldVariant (4 * r + 2) = 0 := by
  rw [paperfoldVariant]
  split_ifs <;> omega

private theorem c_eight_three (r : ℕ) : paperfoldVariant (8 * r + 3) = 1 := by
  rw [paperfoldVariant]
  split_ifs <;> omega

private theorem c_eight_seven (r : ℕ) : paperfoldVariant (8 * r + 7) = 0 := by
  rw [paperfoldVariant]
  split_ifs <;> omega

private theorem c_sixteen_five (r : ℕ) : paperfoldVariant (16 * r + 5) = 1 := by
  rw [paperfoldVariant]
  split_ifs <;> omega

private theorem c_sixteen_thirteen (r : ℕ) : paperfoldVariant (16 * r + 13) = 0 := by
  rw [paperfoldVariant]
  split_ifs <;> omega

private theorem c_halving (r : ℕ) (hr : 0 < r) :
    paperfoldVariant (8 * r + 1) = paperfoldVariant (4 * r + 1) := by
  rw [paperfoldVariant]
  split_ifs <;> try omega
  congr 1
  omega

/-- The induction bridge, with its three precise mathematical inputs explicit.
This is not an assertion that the concrete partition count already supplies those inputs. -/
private theorem complement_of_halving (f : ℕ → ℕ)
    (half : ∀ r, 0 < r → f (2 * r) = f r)
    (one : ∀ s, f (4 * s + 1) = 0)
    (three : ∀ s, f (4 * s + 3) = 1) :
    ∀ r, 0 < r → f r + paperfoldVariant (4 * r + 1) = 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    rcases Nat.even_or_odd' r with ⟨s, hs | hs⟩
    · subst r
      have hs : 0 < s := by omega
      rw [half s hs, show 4 * (2 * s) + 1 = 8 * s + 1 by omega, c_halving s hs]
      exact ih s (by omega) hs
    · subst r
      rcases Nat.even_or_odd' s with ⟨t, ht | ht⟩
      · subst s
        rw [show 2 * (2 * t) + 1 = 4 * t + 1 by omega, one]
        rw [show 4 * (4 * t + 1) + 1 = 16 * t + 5 by omega, c_sixteen_five]
      · subst s
        rw [show 2 * (2 * t + 1) + 1 = 4 * t + 3 by omega, three]
        rw [show 4 * (4 * t + 3) + 1 = 16 * t + 13 by omega, c_sixteen_thirteen]

/-- Explicit inputs corresponding to Corollary 4 with the corrected odd domain.
The two 32-progressions include their zero parameters via the corollary's final
binary-digit assertion; the printed equation (24) alone is restricted to m>0. -/
structure SloaneSellersParity (B : ℕ → ℕ) : Prop where
  odd : ∀ m, 0 < m → B (2 * m + 1) % 2 = (B (2 * m) % 2 + 1) % 2
  eight_two : ∀ m, B (8 * m + 2) % 2 = 1
  eight_six : ∀ m, B (8 * m + 6) % 2 = 0
  sixteen_four : ∀ m, B (16 * m + 4) % 2 = 0
  sixteen_twelve : ∀ m, B (16 * m + 12) % 2 = 1
  sixteen_zero : ∀ m, 0 < m → B (16 * m) % 2 = B (8 * m) % 2
  thirtytwo_eight : ∀ m, B (32 * m + 8) % 2 = 0
  thirtytwo_twentyfour : ∀ m, B (32 * m + 24) % 2 = 1

private theorem parity_halving (B : ℕ → ℕ) (hB : SloaneSellersParity B)
    (r : ℕ) (hr : 0 < r) : B (8 * r) % 2 = B (4 * r) % 2 := by
  rcases Nat.even_or_odd' r with ⟨s, hs | hs⟩
  · subst r
    simpa only [show 8 * (2 * s) = 16 * s by omega,
      show 4 * (2 * s) = 8 * s by omega] using hB.sixteen_zero s (by omega)
  · subst r
    rcases Nat.even_or_odd' s with ⟨t, ht | ht⟩
    · subst s
      rw [show 8 * (2 * (2 * t) + 1) = 32 * t + 8 by omega,
        show 4 * (2 * (2 * t) + 1) = 16 * t + 4 by omega,
        hB.thirtytwo_eight, hB.sixteen_four]
    · subst s
      rw [show 8 * (2 * (2 * t + 1) + 1) = 32 * t + 24 by omega,
        show 4 * (2 * (2 * t + 1) + 1) = 16 * t + 12 by omega,
        hB.thirtytwo_twentyfour, hB.sixteen_twelve]

private theorem parity_complement (B : ℕ → ℕ) (hB : SloaneSellersParity B)
    (r : ℕ) (hr : 0 < r) : B (4 * r) % 2 + paperfoldVariant (4 * r + 1) = 1 := by
  apply complement_of_halving (fun r => B (4 * r) % 2) ?_ ?_ ?_ r hr
  · intro s hs
    simpa only [show 4 * (2 * s) = 8 * s by omega] using parity_halving B hB s hs
  · intro s
    simpa only [show 4 * (4 * s + 1) = 16 * s + 4 by omega] using hB.sixteen_four s
  · intro s
    simpa only [show 4 * (4 * s + 3) = 16 * s + 12 by omega] using hB.sixteen_twelve s

private theorem diff_four (B : ℕ → ℕ) (hB : SloaneSellersParity B)
    (r : ℕ) (hr : 0 < r) :
    (-1 : ℤ) ^ ((4 * r) / 2) * (B (4 * r) % 2 : ℕ) =
      (paperfoldVariant (4 * r) : ℤ) - paperfoldVariant (4 * r + 1) := by
  rw [show 4 * r / 2 = 2 * r by omega, pow_mul, neg_one_sq, one_pow, one_mul, c_four r hr]
  have h : ((B (4 * r) % 2 : ℕ) : ℤ) + (paperfoldVariant (4 * r + 1) : ℤ) = 1 := by
    exact_mod_cast parity_complement B hB r hr
  norm_num only [Int.natCast_one]
  linarith

private theorem diff_four_one (B : ℕ → ℕ) (hB : SloaneSellersParity B)
    (r : ℕ) (hr : 0 < r) :
    (-1 : ℤ) ^ ((4 * r + 1) / 2) * (B (4 * r + 1) % 2 : ℕ) =
      (paperfoldVariant (4 * r + 1) : ℤ) - paperfoldVariant (4 * r + 2) := by
  rw [show (4 * r + 1) / 2 = 2 * r by omega, pow_mul, neg_one_sq, one_pow,
    one_mul, c_four_two]
  have hb := parity_complement B hB r hr
  have ho := hB.odd (2 * r) (by omega)
  have hp := Nat.mod_lt (B (4 * r)) (by decide : 0 < 2)
  have he : B (4 * r + 1) % 2 = paperfoldVariant (4 * r + 1) := by
    rw [show 2 * (2 * r) = 4 * r by omega] at ho
    omega
  simpa only [Int.natCast_zero, sub_zero] using congrArg (fun t : ℕ => (t : ℤ)) he

private theorem diff_four_two (B : ℕ → ℕ) (hB : SloaneSellersParity B) (r : ℕ) :
    (-1 : ℤ) ^ ((4 * r + 2) / 2) * (B (4 * r + 2) % 2 : ℕ) =
      (paperfoldVariant (4 * r + 2) : ℤ) - paperfoldVariant (4 * r + 3) := by
  rw [show (4 * r + 2) / 2 = 2 * r + 1 by omega, pow_succ, pow_mul,
    neg_one_sq, one_pow, one_mul, c_four_two]
  rcases Nat.even_or_odd' r with ⟨s, hs | hs⟩
  · subst r
    rw [show 4 * (2 * s) + 2 = 8 * s + 2 by omega,
      show 4 * (2 * s) + 3 = 8 * s + 3 by omega, hB.eight_two, c_eight_three]
    norm_num
  · subst r
    rw [show 4 * (2 * s + 1) + 2 = 8 * s + 6 by omega,
      show 4 * (2 * s + 1) + 3 = 8 * s + 7 by omega, hB.eight_six, c_eight_seven]
    norm_num

private theorem diff_four_three (B : ℕ → ℕ) (hB : SloaneSellersParity B) (r : ℕ) :
    (-1 : ℤ) ^ ((4 * r + 3) / 2) * (B (4 * r + 3) % 2 : ℕ) =
      (paperfoldVariant (4 * r + 3) : ℤ) - paperfoldVariant (4 * r + 4) := by
  rw [show (4 * r + 3) / 2 = 2 * r + 1 by omega, pow_succ, pow_mul,
    neg_one_sq, one_pow, one_mul, show 4 * r + 4 = 4 * (r + 1) by omega,
    c_four (r + 1) (by omega)]
  have ho := hB.odd (2 * r + 1) (by omega)
  rw [show 2 * (2 * r + 1) = 4 * r + 2 by omega,
    show 4 * r + 2 + 1 = 4 * r + 3 by omega] at ho
  rw [ho]
  rcases Nat.even_or_odd' r with ⟨s, hs | hs⟩
  · subst r
    rw [show 4 * (2 * s) + 2 = 8 * s + 2 by omega,
      show 4 * (2 * s) + 3 = 8 * s + 3 by omega, hB.eight_two, c_eight_three]
    norm_num
  · subst r
    rw [show 4 * (2 * s + 1) + 2 = 8 * s + 6 by omega,
      show 4 * (2 * s + 1) + 3 = 8 * s + 7 by omega, hB.eight_six, c_eight_seven]
    norm_num

/-- Conditional reduction only: its B parity premise is not discharged here. -/
private theorem signed_diff_of_parity (B : ℕ → ℕ) (hB : SloaneSellersParity B)
    (n : ℕ) (hn : 2 ≤ n) :
    (-1 : ℤ) ^ (n / 2) * (B n % 2 : ℕ) =
      (paperfoldVariant n : ℤ) - paperfoldVariant (n + 1) := by
  have hrem : n % 4 < 4 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div n 4
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h
  · have he : n = 4 * (n / 4) := by omega
    have := diff_four B hB (n / 4) (by omega)
    simpa only [← he] using this
  · have he : n = 4 * (n / 4) + 1 := by omega
    have := diff_four_one B hB (n / 4) (by omega)
    simpa only [show 4 * (n / 4) + 2 = (4 * (n / 4) + 1) + 1 by omega, ← he] using this
  · have he : n = 4 * (n / 4) + 2 := by omega
    have := diff_four_two B hB (n / 4)
    simpa only [show 4 * (n / 4) + 3 = (4 * (n / 4) + 2) + 1 by omega, ← he] using this
  · have he : n = 4 * (n / 4) + 3 := by omega
    have := diff_four_three B hB (n / 4)
    simpa only [show 4 * (n / 4) + 4 = (4 * (n / 4) + 3) + 1 by omega, ← he] using this

/-- Literal Corollary 4 (21), with the printed unrestricted odd-index quantifier. -/
def printedOddRule : Prop :=
  ∀ n : ℕ, Odd n → (nonsquashingDistinctPartitions n).card % 2 =
    ((nonsquashingDistinctPartitions (n - 1)).card + 1) % 2

private theorem zero_one :
    (nonsquashingDistinctPartitions 0).card = 1 ∧
    (nonsquashingDistinctPartitions 1).card = 1 := by decide

private theorem printed_odd_rule_false : ¬ printedOddRule := by
  intro h
  have h1 := h 1 (by decide)
  have hne : (nonsquashingDistinctPartitions 1).card % 2 ≠
      ((nonsquashingDistinctPartitions (1 - 1)).card + 1) % 2 := by decide
  exact hne h1

private theorem target_at_two :
    (-1 : ℤ) ^ (2 / 2 : ℕ) * ((nonsquashingDistinctPartitions 2).card % 2 : ℕ) =
      (paperfoldVariant 2 : ℤ) - paperfoldVariant 3 := by
  have h : (nonsquashingDistinctPartitions 2).card = 1 := by decide
  rw [show paperfoldVariant 2 = 0 from c_four_two 0,
    show paperfoldVariant 3 = 1 from c_eight_three 0]
  norm_num [h]

private theorem target_at_three :
    (-1 : ℤ) ^ (3 / 2 : ℕ) * ((nonsquashingDistinctPartitions 3).card % 2 : ℕ) =
      (paperfoldVariant 3 : ℤ) - paperfoldVariant 4 := by
  have h : (nonsquashingDistinctPartitions 3).card = 2 := by decide
  rw [show paperfoldVariant 3 = 1 from c_eight_three 0,
    show paperfoldVariant 4 = 1 from c_four 1 (by decide)]
  norm_num [h]

#print axioms printed_odd_rule_false

#print axioms complement_of_halving
#print axioms parity_halving
#print axioms parity_complement
#print axioms signed_diff_of_parity

run_cmd do
  for (consumer, provider) in
      [( ``parity_complement, ``complement_of_halving),
       ( ``diff_four, ``parity_complement),
       ( ``diff_four_one, ``parity_complement),
       ( ``signed_diff_of_parity, ``diff_four),
       ( ``signed_diff_of_parity, ``diff_four_one),
       ( ``signed_diff_of_parity, ``diff_four_two),
       ( ``signed_diff_of_parity, ``diff_four_three)] do
    let some info := (← Lean.getEnv).checked.get.find? consumer
      | throwError "Missing declaration: {consumer}"
    let some value := info.value? (allowOpaque := true)
      | throwError "Missing proof body: {consumer}"
    unless value.getUsedConstants.contains provider do
      throwError "Missing elaborated dependency: {consumer} -> {provider}"
    Lean.logInfo m!"ELABORATED_DEPENDENCY {consumer} -> {provider}"

end A110037Attempt2
