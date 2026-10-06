/- GID: D5/S1/Words/Palindromes/PeriodDoubling/Word
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/Word
   mirror-E: none(waiver:exact-substitution-valuation-identification)
   anchors: []
   utility: none
   digest: Period-doubling substitution iterates agree with valuation parity. -/

/-
proof_shape: content (block_valuation)
escape_witness: Induction on the literal substitution iterates with indexed even and odd letters.
admission_basis: escape-witness
Direct frozen dependencies: D5/S1/Recurrence/Raney/MaximalBlockEvolution.morphismPower
(statement_id: sha256:23a5d6d2d3272f1bc8b6738c46917f60b439f1398a5ae979e0a2f687b0323f61).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Recurrence.Raney.MaximalBlockEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

open TrureTuring.Raney

/-- The source substitution `a → ab, b → aa`, with `a = false` and `b = true`. -/
def pdMorphism (b : Bool) : List Bool := [false, !b]

/-- The literal finite approximant `φ^e(a)`. -/
def pdBlock (e : ℕ) : List Bool := morphismPower pdMorphism e [false]

/-- The `n`th letter of `φ^ω(a)`, taken in an approximant already covering that position. -/
def u_pd (n : ℕ) : Bool := (pdBlock (n + 1))[n]?.getD false

/-- Every finite substitution iterate has the valuation-parity letters. -/
theorem block_valuation (e : ℕ) :
    (pdBlock e).length = 2 ^ e ∧
      ∀ i : ℕ, i < 2 ^ e →
        (pdBlock e)[i]? = some (decide (padicValNat 2 (i + 1) % 2 = 1)) := by
  have flat_length (xs : List Bool) :
      (xs.flatMap pdMorphism).length = 2 * xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.flatMap_cons, pdMorphism, ih]; omega
  have flat_index (xs : List Bool) (i : ℕ) (hi : i < 2 * xs.length) :
      (xs.flatMap pdMorphism)[i]? =
        if i % 2 = 0 then some false else xs[i / 2]?.map Bool.not := by
    induction xs generalizing i with
    | nil => simp only [List.length_nil, Nat.mul_zero] at hi; omega
    | cons x xs ih =>
      by_cases hsmall : i < 2
      · interval_cases i <;> simp [List.flatMap_cons, pdMorphism]
      · have hlarge : 2 ≤ i := by omega
        have htail : i - 2 < 2 * xs.length := by
          simp only [List.length_cons] at hi
          omega
        have hmod : (i - 2) % 2 = i % 2 := by omega
        have hdiv : (i - 2) / 2 = i / 2 - 1 := by omega
        rw [List.flatMap_cons]
        simp only [pdMorphism, List.getElem?_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, if_neg (by omega : ¬i < 2)]
        rw [ih (i - 2) htail, hmod]
        split
        · rfl
        · rw [hdiv]
          simp only [List.getElem?_cons, if_neg (by omega : i / 2 ≠ 0)]
  induction e with
  | zero =>
    constructor
    · rfl
    · intro i hi
      have he : i = 0 := by simpa using hi
      subst i
      simp [pdBlock, morphismPower]
  | succ e ih =>
    have hblock : pdBlock (e + 1) = (pdBlock e).flatMap pdMorphism := rfl
    constructor
    · rw [hblock, flat_length, ih.1, pow_succ]
      omega
    · intro i hi
      have hilen : i < 2 * (pdBlock e).length := by
        rw [ih.1]
        rw [pow_succ] at hi
        omega
      rw [hblock, flat_index _ i hilen]
      by_cases heven : i % 2 = 0
      · rw [if_pos heven]
        have hp : ¬2 ∣ i + 1 := by omega
        rw [padicValNat.eq_zero_of_not_dvd hp]
        rfl
      · rw [if_neg heven]
        have hi' : i / 2 < 2 ^ e := by rw [pow_succ] at hi; omega
        rw [ih.2 (i / 2) hi']
        have hi_eq : i + 1 = 2 * (i / 2 + 1) := by omega
        have hval : padicValNat 2 (i + 1) = 1 + padicValNat 2 (i / 2 + 1) := by
          rw [hi_eq, padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega),
            padicValNat_self]
        rw [hval]
        simp only [Option.map_some, Option.some.injEq]
        by_cases hp : padicValNat 2 (i / 2 + 1) % 2 = 1
        · have hq : (1 + padicValNat 2 (i / 2 + 1)) % 2 ≠ 1 := by omega
          simp [hp, hq]
        · have hq : (1 + padicValNat 2 (i / 2 + 1)) % 2 = 1 := by omega
          simp [hp, hq]

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.block_valuation
