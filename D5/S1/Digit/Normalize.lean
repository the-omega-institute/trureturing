/- GID: D5/S1/Digit/Normalize
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: [gict/v3.6/I.2/definition/1.4, mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: A terminating deterministic local-carry normalizer for raw W digits. -/

import D5.S1.Digit.Carry
import Mathlib.Data.Finsupp.Order

namespace D5.S1.Digit

/-- Number of digit tokens, counting multiplicity. -/
def tokenCount (r : RawDigits) : ℕ :=
  r.sum fun _ coefficient ↦ coefficient

/-- A concave index weight that strictly orients every repeated-digit carry. -/
def carryIndexWeight (i : ℕ) : ℕ :=
  2 * i + if i = 1 then 1 else 0

/-- Sum of index weights over all digit tokens. -/
def indexWeight (r : RawDigits) : ℕ :=
  r.sum fun i coefficient ↦ coefficient * carryIndexWeight i

/-- Lexicographic termination measure: token count first, then weighted positions. -/
def carryMeasure (r : RawDigits) : ℕ × ℕ :=
  (tokenCount r, indexWeight r)

private theorem tokenCount_add (r s : RawDigits) :
    tokenCount (r + s) = tokenCount r + tokenCount s := by
  classical
  simp [tokenCount, Finsupp.sum_add_index]

@[simp] private theorem tokenCount_single (i coefficient : ℕ) :
    tokenCount (Finsupp.single i coefficient) = coefficient := by
  classical
  simp [tokenCount]

private theorem indexWeight_add (r s : RawDigits) :
    indexWeight (r + s) = indexWeight r + indexWeight s := by
  classical
  simp [indexWeight, Finsupp.sum_add_index, add_mul]

@[simp] private theorem indexWeight_single (i coefficient : ℕ) :
    indexWeight (Finsupp.single i coefficient) = coefficient * carryIndexWeight i := by
  classical
  simp [indexWeight]

private theorem carryIndexWeight_double_succ (i : ℕ) :
    carryIndexWeight i + carryIndexWeight (i + 3) <
      2 * carryIndexWeight (i + 2) := by
  by_cases hi0 : i = 0
  · subst i
    norm_num [carryIndexWeight]
    omega
  by_cases hi1 : i = 1
  · subst i
    norm_num [carryIndexWeight]
  simp only [carryIndexWeight]
  simp [hi1, show i + 3 ≠ 1 by omega, show i + 2 ≠ 1 by omega]
  omega

/-- Every local carry strictly decreases the lexicographic carry measure. -/
theorem carryStep_measure_decreases {before after : RawDigits}
    (step : CarryStep before after) :
    Prod.Lex (· < ·) (· < ·) (carryMeasure after) (carryMeasure before) := by
  cases step with
  | adjacent rest i =>
      apply Prod.Lex.left
      simp only [tokenCount_add, tokenCount_single]
      omega
  | double_zero rest =>
      apply Prod.Lex.left
      simp only [tokenCount_add, tokenCount_single]
      omega
  | double_one rest =>
      have hcount :
          tokenCount (rest + Finsupp.single 0 1 + Finsupp.single 2 1) =
            tokenCount (rest + Finsupp.single 1 2) := by
        simp only [tokenCount_add, tokenCount_single]
      rw [carryMeasure, carryMeasure, hcount]
      apply Prod.Lex.right
      norm_num [indexWeight_add, indexWeight_single, carryIndexWeight]
      omega
  | double_succ rest i =>
      have hcount :
          tokenCount (rest + Finsupp.single i 1 + Finsupp.single (i + 3) 1) =
            tokenCount (rest + Finsupp.single (i + 2) 2) := by
        simp only [tokenCount_add, tokenCount_single]
      rw [carryMeasure, carryMeasure, hcount]
      apply Prod.Lex.right
      have hweight := carryIndexWeight_double_succ i
      simp only [indexWeight_add, indexWeight_single]
      omega

/-- Remove a repeated pair and apply the corresponding low or general carry. -/
noncomputable def carryRepeated (r : RawDigits) : ℕ → RawDigits
  | 0 => r - Finsupp.single 0 2 + Finsupp.single 1 1
  | 1 => r - Finsupp.single 1 2 + Finsupp.single 0 1 + Finsupp.single 2 1
  | i + 2 =>
      r - Finsupp.single (i + 2) 2 +
        Finsupp.single i 1 + Finsupp.single (i + 3) 1

private theorem carryRepeated_step {r : RawDigits} {i : ℕ} (hi : 2 ≤ r i) :
    CarryStep r (carryRepeated r i) := by
  have hle : Finsupp.single i 2 ≤ r := Finsupp.single_le_iff.mpr hi
  have hrest :
      r - Finsupp.single i 2 + Finsupp.single i 2 = r :=
    tsub_add_cancel_of_le hle
  rcases i with _ | _ | i
  · have step := CarryStep.double_zero (r - Finsupp.single 0 2)
    rw [hrest] at step
    exact step
  · have step := CarryStep.double_one (r - Finsupp.single 1 2)
    rw [hrest] at step
    exact step
  · have step := CarryStep.double_succ (r - Finsupp.single (i + 2) 2) i
    rw [hrest] at step
    exact step

/-- Remove an occupied adjacent pair and carry it two positions upward. -/
noncomputable def carryAdjacent (r : RawDigits) (i : ℕ) : RawDigits :=
  r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1) +
    Finsupp.single (i + 2) 1

private theorem carryAdjacent_step {r : RawDigits} {i : ℕ}
    (hi : r i = 1) (hnext : r (i + 1) = 1) :
    CarryStep r (carryAdjacent r i) := by
  have hle : Finsupp.single i 1 + Finsupp.single (i + 1) 1 ≤ r := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [hi]
    by_cases hjnext : j = i + 1
    · subst j
      simp [hnext]
    · simp [hj, hjnext]
  have hrest :
      r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1) +
          (Finsupp.single i 1 + Finsupp.single (i + 1) 1) = r :=
    tsub_add_cancel_of_le hle
  have step := CarryStep.adjacent
    (r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1)) i
  rw [add_assoc, hrest] at step
  simpa only [carryAdjacent] using step

/--
One deterministic pass. It carries the least repeated position if one exists;
otherwise it carries the least adjacent occupied pair, and otherwise is the identity.
-/
noncomputable def carryPass (r : RawDigits) : RawDigits :=
  by
    classical
    exact if hrepeat : ∃ i, 2 ≤ r i then
      carryRepeated r (Nat.find hrepeat)
    else if hadjacent : ∃ i, r i = 1 ∧ r (i + 1) = 1 then
      carryAdjacent r (Nat.find hadjacent)
    else
      r

/-- A noncanonical input takes one genuine local carry step. -/
theorem carryPass_step {r : RawDigits} (h : ¬ CanonicalRaw r) :
    CarryStep r (carryPass r) := by
  rw [carryPass]
  split
  next hrepeat =>
    exact carryRepeated_step (Nat.find_spec hrepeat)
  next hrepeat =>
    split
    next hadjacent =>
      exact carryAdjacent_step (Nat.find_spec hadjacent).1
        (Nat.find_spec hadjacent).2
    next hadjacent =>
      exfalso
      apply h
      have hbinary : ∀ i, r i ≤ 1 := by
        intro i
        by_contra hi
        exact hrepeat ⟨i, by omega⟩
      refine ⟨hbinary, ?_⟩
      intro i hi
      by_contra hnext
      apply hadjacent
      refine ⟨i, hi, ?_⟩
      have := hbinary (i + 1)
      omega

/--
Normalize raw W digits by repeatedly applying `carryPass`. Termination is by the
lexicographic pair `(tokenCount, indexWeight)`, never by the invariant raw value.
-/
noncomputable def normalize (r : RawDigits) : RawDigits := by
  classical
  by_cases h : CanonicalRaw r
  · exact r
  · exact normalize (carryPass r)
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

/-- The normalizer reaches its result through zero or more local carry rules. -/
theorem normalize_reachable (r : RawDigits) :
    Relation.ReflTransGen CarryStep r (normalize r) := by
  rw [normalize]
  split
  next => exact Relation.ReflTransGen.refl
  next h =>
    exact (Relation.ReflTransGen.single (carryPass_step h)).trans
      (normalize_reachable (carryPass r))
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

/-- Normalization always stops at binary, nonadjacent raw digits. -/
theorem normalize_canonical (r : RawDigits) : CanonicalRaw (normalize r) := by
  rw [normalize]
  split
  next h => exact h
  next h => exact normalize_canonical (carryPass r)
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

/-- Normalization preserves the represented natural number. -/
theorem rawValue_normalize (r : RawDigits) :
    rawValue (normalize r) = rawValue r := by
  rw [normalize]
  split
  next => rfl
  next h =>
    rw [rawValue_normalize (carryPass r)]
    exact (rawValue_carryStep (carryPass_step h)).symm
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

/-- Canonical raw digits are fixed points of normalization. -/
theorem normalize_eq_of_canonical {r : RawDigits} (h : CanonicalRaw r) :
    normalize r = r := by
  simp [normalize, h]

/-- Two canonical raw W strings with the same value are equal. -/
theorem canonicalRaw_unique {r s : RawDigits}
    (hr : CanonicalRaw r) (hs : CanonicalRaw s)
    (hvalue : rawValue r = rawValue s) : r = s := by
  rw [← rawOfZeckendorf_rawToZeckendorf r,
    ← rawOfZeckendorf_rawToZeckendorf s,
    rawToZeckendorf_eq_zeckendorf hr,
    rawToZeckendorf_eq_zeckendorf hs,
    hvalue]

/-- The local normalizer agrees extensionally with the Zeckendorf specification. -/
theorem normalize_eq_rawOfZeckendorf (r : RawDigits) :
    normalize r = rawOfZeckendorf (Nat.zeckendorf (rawValue r)) := by
  have hzeckendorf : (Nat.zeckendorf (rawValue r)).IsZeckendorfRep :=
    Nat.isZeckendorfRep_zeckendorf _
  apply canonicalRaw_unique (normalize_canonical r)
    (canonicalRaw_rawOfZeckendorf hzeckendorf)
  rw [rawValue_normalize, rawValue_rawOfZeckendorf hzeckendorf,
    Nat.sum_zeckendorf_fib]

end D5.S1.Digit
