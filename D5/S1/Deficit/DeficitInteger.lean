/- GID: D5/S1/Deficit/DeficitInteger
   generality: I
   mirror-B: D5/B/S1/Deficit/DeficitInteger
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   digest: The normalized beta deficit of golden addition is an integer counting bottom carries. -/

import D5.S1.Digit.Addition
import D5.S1.Scale.Embedding
import D5.S0.Carrier.Conj
import Mathlib.Tactic.LinearCombination

namespace D5.S1.Deficit

open D5.S1.Digit

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Scale

/-! ### Golden coordinate helpers and the golden fixed-point recurrence -/

@[simp] private theorem b_sub (x y : GoldenInt) : (x - y).b = x.b - y.b := by
  rw [sub_eq_add_neg, b_add, b_neg]; ring

/-- The golden fixed-point recurrence on integer powers. -/
private theorem phi_pow_carry (n : ℕ) : phi ^ (n + 2) = phi ^ (n + 1) + phi ^ n := by
  rw [pow_add, phi_sq]; ring

private theorem phi_pow_b_aux (n : ℕ) :
    (phi ^ n).b = (Nat.fib n : ℤ) ∧ (phi ^ (n + 1)).b = (Nat.fib (n + 1) : ℤ) := by
  induction n with
  | zero => exact ⟨by simp, by simp [phi]⟩
  | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [phi_pow_carry n, b_add, ih.2, ih.1, Nat.fib_add_two]
      push_cast; ring

/-- The `phi`-coordinate of an integer golden power is its Fibonacci number. -/
private theorem phi_pow_b (n : ℕ) : (phi ^ n).b = (Nat.fib n : ℤ) :=
  (phi_pow_b_aux n).1

/-- Three golden identities that carry the whole deficit: each is a consequence of
`phi ^ 2 = phi + 1` and reduces the corresponding carry rule to an integer. -/
private theorem phi_key_adjacent : (1 : GoldenInt) + phi - phi ^ 2 = 0 := by
  rw [phi_sq]; ring

private theorem phi_key_low : (2 : GoldenInt) * phi ^ 2 - 1 - phi ^ 3 = 0 := by
  have h3 : phi ^ 3 = phi ^ 2 + phi := by have := phi_pow_carry 1; simpa using this
  rw [h3, phi_sq]; ring

private theorem phi_key_second : (2 : GoldenInt) * phi ^ 3 - phi ^ 2 - phi ^ 4 = -1 := by
  have h3 : phi ^ 3 = phi ^ 2 + phi := by have := phi_pow_carry 1; simpa using this
  have h4 : phi ^ 4 = phi ^ 3 + phi ^ 2 := by have := phi_pow_carry 2; simpa using this
  rw [h4, h3, phi_sq]; ring

/-! ### The golden model-set evaluation of raw digits -/

/-- The expansion-face model-set value of raw W digits, valued in `ℤ[φ]`.
The `W_i` weight is carried by the golden power `phi ^ (i + 2)`. -/
noncomputable def betaDigits (r : RawDigits) : GoldenInt :=
  r.sum fun i coefficient ↦ (coefficient : GoldenInt) * phi ^ (i + 2)

private theorem betaDigits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast; ring

@[simp] private theorem betaDigits_single (i coefficient : ℕ) :
    betaDigits (Finsupp.single i coefficient) = (coefficient : GoldenInt) * phi ^ (i + 2) := by
  classical
  rw [betaDigits, Finsupp.sum_single_index (by simp)]

/-- The `phi`-coordinate of the model-set value is exactly the raw natural value.
This is the additivity of `beta - beta' = sqrt 5 * v`: the internal (contraction)
face differs from the expansion face by `sqrt 5` times this coordinate. -/
private theorem betaDigits_b (r : RawDigits) : (betaDigits r).b = (rawValue r : ℤ) := by
  classical
  induction r using Finsupp.induction with
  | zero => simp [betaDigits, rawValue]
  | single_add i coefficient f _ _ ih =>
      rw [betaDigits_add, b_add, betaDigits_single, ih, rawValue_add, rawValue_single,
        b_mul, a_natCast, b_natCast, phi_pow_b]
      simp only [wValue]
      push_cast; ring

/-! ### Per-carry deficits: internal carries lose nothing, bottom carries lose a unit -/

/-- The lowest repeated carry `2 W_0 = W_1` hides one positive unit. -/
private theorem betaDigits_carryRepeated_zero {r : RawDigits} (h : 2 ≤ r 0) :
    betaDigits r - betaDigits (carryRepeated r 0) = 1 := by
  have hle : Finsupp.single 0 2 ≤ r := Finsupp.single_le_iff.mpr h
  have hsplit : betaDigits (r - Finsupp.single 0 2) + betaDigits (Finsupp.single 0 2)
      = betaDigits r := by
    rw [← betaDigits_add, tsub_add_cancel_of_le hle]
  have hcr : carryRepeated r 0 = r - Finsupp.single 0 2 + Finsupp.single 1 1 := rfl
  rw [hcr, betaDigits_add, ← hsplit, betaDigits_single, betaDigits_single]
  push_cast
  linear_combination phi_key_low

/-- The second repeated carry `2 W_1 = W_0 + W_2` hides one negative unit. -/
private theorem betaDigits_carryRepeated_one {r : RawDigits} (h : 2 ≤ r 1) :
    betaDigits r - betaDigits (carryRepeated r 1) = -1 := by
  have hle : Finsupp.single 1 2 ≤ r := Finsupp.single_le_iff.mpr h
  have hsplit : betaDigits (r - Finsupp.single 1 2) + betaDigits (Finsupp.single 1 2)
      = betaDigits r := by
    rw [← betaDigits_add, tsub_add_cancel_of_le hle]
  have hcr : carryRepeated r 1 =
      r - Finsupp.single 1 2 + Finsupp.single 0 1 + Finsupp.single 2 1 := rfl
  rw [hcr, betaDigits_add, betaDigits_add, ← hsplit, betaDigits_single, betaDigits_single,
    betaDigits_single]
  push_cast
  linear_combination phi_key_second

/-- Every higher repeated carry `2 W_(i+2) = W_i + W_(i+3)` is exactly value-neutral. -/
private theorem betaDigits_carryRepeated_succ {r : RawDigits} {i : ℕ} (h : 2 ≤ r (i + 2)) :
    betaDigits r - betaDigits (carryRepeated r (i + 2)) = 0 := by
  have hle : Finsupp.single (i + 2) 2 ≤ r := Finsupp.single_le_iff.mpr h
  have hsplit : betaDigits (r - Finsupp.single (i + 2) 2) + betaDigits (Finsupp.single (i + 2) 2)
      = betaDigits r := by
    rw [← betaDigits_add, tsub_add_cancel_of_le hle]
  have hcr : carryRepeated r (i + 2) =
      r - Finsupp.single (i + 2) 2 + Finsupp.single i 1 + Finsupp.single (i + 3) 1 := rfl
  rw [hcr, betaDigits_add, betaDigits_add, ← hsplit, betaDigits_single, betaDigits_single,
    betaDigits_single]
  push_cast
  linear_combination (phi ^ (i + 2)) * phi_key_low

/-- The adjacent carry `W_i + W_(i+1) = W_(i+2)` is exactly value-neutral. -/
private theorem betaDigits_carryAdjacent {r : RawDigits} {i : ℕ}
    (hi : r i = 1) (hn : r (i + 1) = 1) :
    betaDigits r - betaDigits (carryAdjacent r i) = 0 := by
  have hle : Finsupp.single i 1 + Finsupp.single (i + 1) 1 ≤ r := by
    intro j
    by_cases hj : j = i
    · subst j; simp [hi]
    by_cases hj' : j = i + 1
    · subst j; simp [hn]
    · simp [hj, hj']
  have hS : betaDigits r = betaDigits (r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1))
      + (betaDigits (Finsupp.single i 1) + betaDigits (Finsupp.single (i + 1) 1)) := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [betaDigits_add, betaDigits_add]
  have hca : carryAdjacent r i =
      r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1) + Finsupp.single (i + 2) 1 := rfl
  rw [hca, betaDigits_add, hS, betaDigits_single, betaDigits_single, betaDigits_single]
  push_cast
  linear_combination (phi ^ (i + 2)) * phi_key_adjacent

/-! ### The signed count of bottom-carry events along normalization -/

/-- The signed unit contributed by the single carry rule that `carryPass` fires:
`+1` for the lowest repeated carry, `-1` for the second, and `0` for every
internal carry (higher repeated or adjacent). -/
noncomputable def carrySign (r : RawDigits) : ℤ := by
  classical
  exact if hrep : ∃ i, 2 ≤ r i then
      (if Nat.find hrep = 0 then 1 else if Nat.find hrep = 1 then -1 else 0)
    else 0

/-- The signed count of bottom-carry events fired while normalizing raw digits. -/
noncomputable def carrySignedCount (r : RawDigits) : ℤ := by
  classical
  by_cases h : CanonicalRaw r
  · exact 0
  · exact carrySign r + carrySignedCount (carryPass r)
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

private theorem carrySignedCount_canonical {r : RawDigits} (h : CanonicalRaw r) :
    carrySignedCount r = 0 := by
  rw [carrySignedCount]; simp [h]

private theorem carrySignedCount_not_canonical {r : RawDigits} (h : ¬ CanonicalRaw r) :
    carrySignedCount r = carrySign r + carrySignedCount (carryPass r) := by
  conv_lhs => rw [carrySignedCount]
  rw [dif_neg h]

private theorem normalize_not_canonical {r : RawDigits} (h : ¬ CanonicalRaw r) :
    normalize r = normalize (carryPass r) := by
  conv_lhs => rw [D5.S1.Digit.normalize]
  rw [dif_neg h]

/-- One `carryPass` shifts the model-set value by exactly its signed carry unit. -/
private theorem betaDigits_sub_carryPass (r : RawDigits) :
    betaDigits r - betaDigits (carryPass r) = ((carrySign r : ℤ) : GoldenInt) := by
  classical
  rw [carryPass, carrySign]
  by_cases hrep : ∃ i, 2 ≤ r i
  · simp only [dif_pos hrep]
    have hspec : 2 ≤ r (Nat.find hrep) := Nat.find_spec hrep
    obtain hj | hj | ⟨k, hj⟩ :
        Nat.find hrep = 0 ∨ Nat.find hrep = 1 ∨ ∃ k, Nat.find hrep = k + 2 := by
      rcases Nat.find hrep with _ | _ | k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨k, rfl⟩)
    · rw [hj] at hspec ⊢
      rw [betaDigits_carryRepeated_zero hspec]; simp
    · rw [hj] at hspec ⊢
      rw [betaDigits_carryRepeated_one hspec]; simp
    · rw [hj] at hspec ⊢
      rw [betaDigits_carryRepeated_succ hspec, if_neg (by omega : ¬ k + 2 = 0),
        if_neg (by omega : ¬ k + 2 = 1)]; simp
  · simp only [dif_neg hrep]
    by_cases hadj : ∃ i, r i = 1 ∧ r (i + 1) = 1
    · simp only [dif_pos hadj]
      obtain ⟨hi, hn⟩ := Nat.find_spec hadj
      rw [betaDigits_carryAdjacent hi hn]; simp
    · simp only [dif_neg hadj]; simp

/-- The total model-set deficit of normalization equals the signed bottom-carry count. -/
private theorem betaDeficit_eq_count (r : RawDigits) :
    betaDigits r - betaDigits (normalize r) = ((carrySignedCount r : ℤ) : GoldenInt) := by
  by_cases h : CanonicalRaw r
  · rw [normalize_eq_of_canonical h, carrySignedCount_canonical h]; simp
  · rw [normalize_not_canonical h, carrySignedCount_not_canonical h, Int.cast_add,
      ← betaDeficit_eq_count (carryPass r), ← betaDigits_sub_carryPass r]
    ring
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

/-! ### The real deficit and its integer certificate -/

/-- The expansion-face model-set value of a natural number. -/
noncomputable def betaGolden (v : ℕ) : GoldenInt := betaDigits (toRaw (Z v))

/-- The real model-set value `beta v`. -/
noncomputable def betaReal (v : ℕ) : ℝ := embedding (betaGolden v)

/-- The internal (contraction) face `beta' v`, the Galois conjugate value. -/
noncomputable def betaContraction (v : ℕ) : ℝ := embedding (conj (betaGolden v))

/-- The normalization deficit `c(v₁, v₂) := beta v₁ + beta v₂ - beta (v₁ + v₂)`. -/
noncomputable def deficit (v₁ v₂ : ℕ) : ℝ :=
  betaReal v₁ + betaReal v₂ - betaReal (v₁ + v₂)

/-- The same deficit read on the contraction face. -/
noncomputable def deficitContraction (v₁ v₂ : ℕ) : ℝ :=
  betaContraction v₁ + betaContraction v₂ - betaContraction (v₁ + v₂)

/-- The deficit as a golden integer. -/
noncomputable def deficitGolden (v₁ v₂ : ℕ) : GoldenInt :=
  betaGolden v₁ + betaGolden v₂ - betaGolden (v₁ + v₂)

private theorem deficitGolden_eq (v₁ v₂ : ℕ) :
    deficitGolden v₁ v₂ = betaDigits (toRaw (Z v₁) + toRaw (Z v₂))
      - betaDigits (normalize (toRaw (Z v₁) + toRaw (Z v₂))) := by
  rw [deficitGolden, betaGolden, betaGolden, betaGolden, ← betaDigits_add, zeck_add]

private theorem deficitGolden_b (v₁ v₂ : ℕ) : (deficitGolden v₁ v₂).b = 0 := by
  rw [deficitGolden_eq, b_sub, betaDigits_b, betaDigits_b, rawValue_normalize, sub_self]

private theorem conj_sub (x y : GoldenInt) : conj (x - y) = conj x - conj y := by
  ext <;> simp [conj, sub_eq_add_neg] <;> ring

private theorem conj_deficitGolden (v₁ v₂ : ℕ) :
    conj (deficitGolden v₁ v₂) = deficitGolden v₁ v₂ := by
  have hb := deficitGolden_b v₁ v₂
  apply GoldenInt.ext <;> simp [conj, hb]

private theorem deficit_eq_embedding (v₁ v₂ : ℕ) :
    deficit v₁ v₂ = embedding (deficitGolden v₁ v₂) := by
  simp only [deficit, betaReal, deficitGolden, map_add, map_sub]

private theorem deficitContraction_eq_embedding (v₁ v₂ : ℕ) :
    deficitContraction v₁ v₂ = embedding (conj (deficitGolden v₁ v₂)) := by
  simp only [deficitContraction, betaContraction, deficitGolden, conj_add, conj_sub,
    map_add, map_sub]

private theorem deficit_eq_deficitContraction (v₁ v₂ : ℕ) :
    deficit v₁ v₂ = deficitContraction v₁ v₂ := by
  rw [deficit_eq_embedding, deficitContraction_eq_embedding, conj_deficitGolden]

/-! ### The normalized beta-deficit integer theorem -/

/-- The normalized golden-addition deficit is an integer counting bottom carries.
Clause (i): the deficit read on the expansion face equals the deficit read on the
contraction (Galois) face, because the two faces differ by an additive term that
cancels in the deficit. Clause (ii): the deficit is a rational integer. Clause (iii):
that integer is the signed count of the two bottom carry rules fired during
normalization, all internal carries being value-neutral. -/
theorem deficit_integer (v₁ v₂ : ℕ) :
    deficit v₁ v₂ = deficitContraction v₁ v₂ ∧
      (∃ z : ℤ, deficit v₁ v₂ = (z : ℝ)) ∧
      deficit v₁ v₂ = (carrySignedCount (toRaw (Z v₁) + toRaw (Z v₂)) : ℝ) := by
  refine ⟨deficit_eq_deficitContraction v₁ v₂, ⟨(deficitGolden v₁ v₂).a, ?_⟩, ?_⟩
  · rw [deficit_eq_embedding, embedding_apply, deficitGolden_b]; simp
  · rw [deficit_eq_embedding, deficitGolden_eq, betaDeficit_eq_count, map_intCast]

end D5.S1.Deficit
