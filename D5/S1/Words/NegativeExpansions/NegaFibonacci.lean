/- GID: D5/S1/Words/NegativeExpansions/NegaFibonacci
   generality: I
   mirror-B: none(waiver:negative-fibonacci-support)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Canonical negative-Fibonacci words represent exact alternating intervals. -/

import D5.S1.Scale.Fibonacci
import Mathlib.Algebra.Ring.Parity

namespace D5.S1.Words.NegativeExpansions.NegaFibonacci

open D5.S1.Scale

/-- Binary words with no adjacent occupied positions, written deepest digit first. -/
def Canonical : List Nat → Prop
  | [] => True
  | digit :: tail =>
      digit ≤ 1 ∧
        (match tail with
          | [] => True
          | next :: _ => digit = 1 → next = 0) ∧
        Canonical tail

def Compatible (left right : Nat) : Prop := left = 0 ∨ right = 0

private theorem canonical_bounds : ∀ {digits : List Nat},
    Canonical digits → ∀ digit ∈ digits, digit ≤ 1
  | [], _ => by simp
  | current :: tail, h => by
      intro digit hdigit
      simp only [List.mem_cons] at hdigit
      rcases hdigit with heq | hdigit
      · exact heq ▸ h.1
      · exact canonical_bounds h.2.2 digit hdigit

private theorem canonical_chain : ∀ {digits : List Nat},
    Canonical digits → digits.IsChain Compatible
  | [], _ => by simp
  | [_], _ => by simp
  | current :: next :: tail, h => by
      rw [List.isChain_cons_cons]
      constructor
      · by_cases hzero : current = 0
        · exact Or.inl hzero
        · exact Or.inr (h.2.1 (by have := h.1; omega))
      · exact canonical_chain h.2.2

private theorem canonical_of_bounds_chain : ∀ {digits : List Nat},
    (∀ digit ∈ digits, digit ≤ 1) → digits.IsChain Compatible → Canonical digits
  | [], _, _ => trivial
  | [current], hbounds, _ => by
      simp only [Canonical]
      exact ⟨hbounds current (by simp), trivial, trivial⟩
  | current :: next :: tail, hbounds, hchain => by
      rw [Canonical]
      have hpair := (List.isChain_cons_cons.mp hchain).1
      refine ⟨hbounds current (by simp), ?_, ?_⟩
      · intro hcurrent
        rcases hpair with hzero | hnext
        · omega
        · exact hnext
      · exact canonical_of_bounds_chain
          (fun digit hdigit => hbounds digit (by simp [hdigit]))
          (List.isChain_cons_cons.mp hchain).2

/-- Reversing a canonical word preserves binary non-adjacency. -/
theorem canonical_reverse {digits : List Nat} (h : Canonical digits) :
    Canonical digits.reverse := by
  apply canonical_of_bounds_chain
  · intro digit hdigit
    exact canonical_bounds h digit (by simpa using hdigit)
  · rw [List.isChain_reverse]
    apply List.IsChain.imp (p := canonical_chain h)
    intro left right hcompatible
    rcases hcompatible with hleft | hright
    · exact Or.inr hleft
    · exact Or.inl hright

theorem canonical_append {left right : List Nat}
    (hleft : Canonical left) (hright : Canonical right)
    (hboundary : ∀ x ∈ left.getLast?, ∀ y ∈ right.head?, Compatible x y) :
    Canonical (left ++ right) := by
  apply canonical_of_bounds_chain
  · intro digit hdigit
    rcases List.mem_append.mp hdigit with hmem | hmem
    · exact canonical_bounds hleft digit hmem
    · exact canonical_bounds hright digit hmem
  · rw [List.isChain_append]
    exact ⟨canonical_chain hleft, canonical_chain hright, hboundary⟩

theorem canonical_zero_cons {digits : List Nat} (h : Canonical digits) :
    Canonical (0 :: digits) := by
  cases digits <;> simp_all [Canonical]

theorem canonical_take (n : Nat) {digits : List Nat} (h : Canonical digits) :
    Canonical (digits.take n) := by
  apply canonical_of_bounds_chain
  · intro digit hdigit
    exact canonical_bounds h digit (List.mem_of_mem_take hdigit)
  · exact (canonical_chain h).take n

theorem canonical_drop (n : Nat) {digits : List Nat} (h : Canonical digits) :
    Canonical (digits.drop n) := by
  apply canonical_of_bounds_chain
  · intro digit hdigit
    exact canonical_bounds h digit (List.mem_of_mem_drop hdigit)
  · exact (canonical_chain h).drop n

/-- The signed Fibonacci weight of a deepest-digit-first word. -/
def weight : List Nat → Int
  | [] => 0
  | digit :: tail =>
      (digit : Int) * (-1 : Int) ^ (tail.length + 1) * Nat.fib (tail.length + 1) +
        weight tail

def Represents (n : Nat) (value : Int) : Prop :=
  ∃ digits : List Nat,
    digits.length = n ∧ Canonical digits ∧ weight digits = value

def lower (n : Nat) : Int :=
  if Even n then -(Nat.fib n : Int) else -(Nat.fib (n + 1) : Int)

def upper (n : Nat) : Int :=
  if Even n then (Nat.fib (n + 1) : Int) - 1 else (Nat.fib n : Int) - 1

private theorem even_add_two_iff (n : Nat) : Even (n + 2) ↔ Even n := by
  constructor
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by omega
    refine ⟨k - 1, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩

private theorem even_succ_iff_not_even (n : Nat) : Even (n + 1) ↔ ¬ Even n := by
  constructor
  · rintro ⟨k, hk⟩ ⟨j, hj⟩
    omega
  · intro hn
    exact (Nat.not_even_iff_odd.mp hn).add_one

private theorem odd_add_two_iff (n : Nat) : Odd (n + 2) ↔ Odd n := by
  constructor
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by omega
    refine ⟨k - 1, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩

private theorem fib_add_two_int (n : Nat) :
    (Nat.fib (n + 2) : Int) = Nat.fib (n + 1) + Nat.fib n := by
  rw [Nat.fib_add_two]
  push_cast
  ring

private theorem weight_zero_cons (digits : List Nat) :
    weight (0 :: digits) = weight digits := by simp [weight]

private theorem weight_one_zero_cons (digits : List Nat) :
    weight (1 :: 0 :: digits) =
      (-1 : Int) ^ (digits.length + 2) * Nat.fib (digits.length + 2) +
        weight digits := by
  simp [weight]

private theorem canonical_one_zero_cons {digits : List Nat} (h : Canonical digits) :
    Canonical (1 :: 0 :: digits) := by
  cases digits <;> simp_all [Canonical]

private theorem interval_even_step {n : Nat} (hn : Even n) :
    lower (n + 2) = lower (n + 1) ∧
      upper (n + 1) + 1 =
        (Nat.fib (n + 2) : Int) + lower n ∧
      (Nat.fib (n + 2) : Int) + upper n = upper (n + 2) := by
  have hn2 : Even (n + 2) := (even_add_two_iff n).2 hn
  have hn1 : ¬ Even (n + 1) := by
    intro h
    exact (even_succ_iff_not_even n).1 h hn
  have hrec1 : (Nat.fib (n + 3) : Int) =
      Nat.fib (n + 2) + Nat.fib (n + 1) := by
    simpa only [show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 1 = n + 2 by omega] using fib_add_two_int (n + 1)
  constructor
  · simp only [lower, if_pos hn2, if_neg hn1]
  · constructor
    · simp only [upper, lower, if_neg hn1, if_pos hn]
      rw [show n + 1 + 1 = n + 2 by omega, fib_add_two_int]
      ring
    · simp only [upper, if_pos hn, if_pos hn2]
      rw [show n + 2 + 1 = n + 3 by omega, hrec1]
      ring

private theorem interval_odd_step {n : Nat} (hn : ¬ Even n) :
    lower (n + 2) =
        -(Nat.fib (n + 2) : Int) + lower n ∧
      -(Nat.fib (n + 2) : Int) + upper n + 1 = lower (n + 1) ∧
      upper (n + 1) = upper (n + 2) := by
  have hn2 : ¬ Even (n + 2) := by
    intro h
    exact hn ((even_add_two_iff n).1 h)
  have hn1 : Even (n + 1) := (even_succ_iff_not_even n).2 hn
  have hrec1 : (Nat.fib (n + 3) : Int) =
      Nat.fib (n + 2) + Nat.fib (n + 1) := by
    simpa only [show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 1 = n + 2 by omega] using fib_add_two_int (n + 1)
  constructor
  · simp only [lower, if_neg hn2, if_neg hn]
    rw [show n + 2 + 1 = n + 3 by omega,
      show n + 1 = n + 1 by rfl, hrec1]
    ring
  · constructor
    · simp only [upper, lower, if_neg hn, if_pos hn1]
      rw [fib_add_two_int]
      ring
    · simp only [upper, if_pos hn1, if_neg hn2]

private theorem lower_le_upper (n : Nat) : lower n ≤ upper n := by
  by_cases hn : Even n
  · have hpos : 0 < Nat.fib (n + 1) := Nat.fib_pos.2 (by omega)
    simp [lower, upper, hn]
    omega
  · have hnpos : 0 < n := by
      by_contra hzero
      have : n = 0 := by omega
      subst n
      exact hn ⟨0, rfl⟩
    have hpos : 0 < Nat.fib n := Nat.fib_pos.2 hnpos
    simp [lower, upper, hn]
    omega

/-- Every integer in the parity-dependent length-`n` interval has a canonical
negative-Fibonacci representation of exactly that length. -/
theorem represents_of_mem_interval : ∀ n : Nat, ∀ value : Int,
    lower n ≤ value → value ≤ upper n → Represents n value := by
  apply Nat.twoStepInduction
  · intro value hlower hupper
    have hvalue : value = 0 := by
      norm_num [lower, upper, Nat.fib] at hlower hupper ⊢
      omega
    subst value
    exact ⟨[], rfl, trivial, rfl⟩
  · intro value hlower hupper
    have hvalue : value = -1 ∨ value = 0 := by
      norm_num [lower, upper, Nat.fib] at hlower hupper ⊢
      omega
    rcases hvalue with rfl | rfl
    · exact ⟨[1], rfl, by norm_num [Canonical], by norm_num [weight]⟩
    · exact ⟨[0], rfl, by norm_num [Canonical], by norm_num [weight]⟩
  · intro n hn hn1 value hlower hupper
    by_cases heven : Even n
    · obtain ⟨hlowerEq, hjoin, hupperEq⟩ := interval_even_step heven
      by_cases hleft : value ≤ upper (n + 1)
      · obtain ⟨digits, hlength, hcanonical, hweight⟩ :=
          hn1 value (by omega) hleft
        refine ⟨0 :: digits, by simp [hlength], canonical_zero_cons hcanonical, ?_⟩
        rw [weight_zero_cons, hweight]
      · let shifted := value - (Nat.fib (n + 2) : Int)
        have hshiftLower : lower n ≤ shifted := by omega
        have hshiftUpper : shifted ≤ upper n := by omega
        obtain ⟨digits, hlength, hcanonical, hweight⟩ :=
          hn shifted hshiftLower hshiftUpper
        refine ⟨1 :: 0 :: digits, by simp [hlength],
          canonical_one_zero_cons hcanonical, ?_⟩
        have heven2 : Even (n + 2) := (even_add_two_iff n).2 heven
        rw [weight_one_zero_cons, hlength, heven2.neg_one_pow, hweight]
        dsimp [shifted]
        ring
    · obtain ⟨hlowerEq, hjoin, hupperEq⟩ := interval_odd_step heven
      by_cases hright : lower (n + 1) ≤ value
      · obtain ⟨digits, hlength, hcanonical, hweight⟩ :=
          hn1 value hright (by omega)
        refine ⟨0 :: digits, by simp [hlength], canonical_zero_cons hcanonical, ?_⟩
        rw [weight_zero_cons, hweight]
      · let shifted := value + (Nat.fib (n + 2) : Int)
        have hinterval := lower_le_upper n
        have hshiftLower : lower n ≤ shifted := by omega
        have hshiftUpper : shifted ≤ upper n := by omega
        obtain ⟨digits, hlength, hcanonical, hweight⟩ :=
          hn shifted hshiftLower hshiftUpper
        have hodd : Odd n := Nat.not_even_iff_odd.mp heven
        have hodd2 : Odd (n + 2) := (odd_add_two_iff n).2 hodd
        refine ⟨1 :: 0 :: digits, by simp [hlength],
          canonical_one_zero_cons hcanonical, ?_⟩
        rw [weight_one_zero_cons, hlength, hodd2.neg_one_pow, hweight]
        dsimp [shifted]
        ring

theorem mem_interval_of_represents : ∀ n : Nat, ∀ value : Int,
    Represents n value → lower n ≤ value ∧ value ≤ upper n := by
  apply Nat.twoStepInduction
  · intro value hrep
    obtain ⟨digits, hlength, _, hweight⟩ := hrep
    have : digits = [] := List.eq_nil_of_length_eq_zero hlength
    subst digits
    norm_num [lower, upper, weight] at hweight ⊢
    omega
  · intro value hrep
    obtain ⟨digits, hlength, hcanonical, hweight⟩ := hrep
    rcases digits with _ | ⟨digit, tail⟩
    · contradiction
    · have htail : tail = [] := List.eq_nil_of_length_eq_zero (by simpa using hlength)
      subst tail
      simp only [Canonical] at hcanonical
      norm_num [lower, upper, weight, Nat.fib] at hweight ⊢
      omega
  · intro n hn hn1 value hrep
    obtain ⟨digits, hlength, hcanonical, hweight⟩ := hrep
    cases digits with
    | nil => simp at hlength
    | cons digit tail =>
        have hdigit : digit = 0 ∨ digit = 1 := by
          have := hcanonical.1
          omega
        rcases hdigit with rfl | rfl
        · have htailLength : tail.length = n + 1 := by simp at hlength; omega
          have htailCanonical : Canonical tail := hcanonical.2.2
          have htailWeight : weight tail = value := by
            simpa [weight] using hweight
          have htailBounds := hn1 value
            ⟨tail, htailLength, htailCanonical, htailWeight⟩
          by_cases heven : Even n
          · obtain ⟨hlowerEq, _, hupperEq⟩ := interval_even_step heven
            have hinterval := lower_le_upper n
            constructor <;> omega
          · obtain ⟨_, _, hupperEq⟩ := interval_odd_step heven
            have hlowerTargetLe : lower (n + 2) ≤ lower (n + 1) := by
              obtain ⟨hlowerEq, hjoin, _⟩ := interval_odd_step heven
              have hupperLower := lower_le_upper n
              omega
            constructor <;> omega
        · cases tail with
          | nil => simp at hlength
          | cons next rest =>
              have hnext : next = 0 := hcanonical.2.1 rfl
              subst next
              have hrestLength : rest.length = n := by simp at hlength; omega
              have hrestCanonical : Canonical rest := hcanonical.2.2.2.2
              have hrestBounds := hn (weight rest)
                ⟨rest, hrestLength, hrestCanonical, rfl⟩
              rw [weight_one_zero_cons, hrestLength] at hweight
              by_cases heven : Even n
              · obtain ⟨hlowerEq, hjoin, hupperEq⟩ := interval_even_step heven
                have heven2 : Even (n + 2) := (even_add_two_iff n).2 heven
                rw [heven2.neg_one_pow] at hweight
                have hinterval := lower_le_upper n
                have hnextInterval := lower_le_upper (n + 1)
                constructor <;> omega
              · obtain ⟨hlowerEq, hjoin, hupperEq⟩ := interval_odd_step heven
                have hodd : Odd n := Nat.not_even_iff_odd.mp heven
                have hodd2 : Odd (n + 2) := (odd_add_two_iff n).2 hodd
                rw [hodd2.neg_one_pow] at hweight
                have hinterval := lower_le_upper n
                have hnextInterval := lower_le_upper (n + 1)
                constructor <;> omega

def trim : List Nat → List Nat
  | [] => []
  | 0 :: tail => trim tail
  | digit :: tail => digit :: tail

private theorem weight_trim : ∀ digits : List Nat, weight (trim digits) = weight digits
  | [] => rfl
  | 0 :: tail => by rw [trim, weight_zero_cons, weight_trim]
  | (digit + 1) :: tail => rfl

private theorem canonical_trim : ∀ {digits : List Nat},
    Canonical digits → Canonical (trim digits)
  | [], _ => trivial
  | 0 :: tail, h => @canonical_trim tail h.2.2
  | (digit + 1) :: tail, h => by simpa [trim] using h

private theorem trim_head_one {digits : List Nat} (hcanonical : Canonical digits)
    (hweight : weight digits ≠ 0) : (trim digits).head? = some 1 := by
  induction digits with
  | nil => simp [weight] at hweight
  | cons digit tail ih =>
      cases digit with
      | zero =>
          apply ih hcanonical.2.2
          rw [weight_zero_cons] at hweight
          exact hweight
      | succ digit =>
          have : digit = 0 := by have := hcanonical.1; omega
          subst digit
          simp [trim]

private theorem trimmed_even_of_pos {digits : List Nat}
    (hcanonical : Canonical digits) (hpositive : 0 < weight digits) :
    Even (trim digits).length := by
  let normalized := trim digits
  have hnormalizedCanonical : Canonical normalized := canonical_trim hcanonical
  have hnormalizedWeight : weight normalized = weight digits := weight_trim digits
  have hhead : normalized.head? = some 1 :=
    trim_head_one hcanonical (by omega)
  have hnormalizedPositive : 0 < weight normalized := by
    rw [hnormalizedWeight]
    exact hpositive
  change Even normalized.length
  cases hnorm : normalized with
  | nil => rw [hnorm] at hhead; simp at hhead
  | cons digit tail =>
      rw [hnorm] at hhead hnormalizedCanonical hnormalizedPositive
      have hdigit : digit = 1 := by
        simpa using hhead
      subst digit
      by_cases heven : Even (tail.length + 1)
      · simpa using heven
      · exfalso
        have hoddLength : Odd (tail.length + 1) :=
          Nat.not_even_iff_odd.mp heven
        cases tail with
        | nil =>
          norm_num [weight] at hnormalizedPositive
        | cons next rest =>
          have hnext : next = 0 := hnormalizedCanonical.2.1 rfl
          subst next
          have hoddRest : Odd rest.length := (odd_add_two_iff rest.length).1 (by
            simpa only [List.length_cons] using hoddLength)
          have hrestBounds := mem_interval_of_represents rest.length (weight rest)
            ⟨rest, rfl, hnormalizedCanonical.2.2.2.2, rfl⟩
          have hrestNotEven : ¬ Even rest.length :=
            Nat.not_even_iff_odd.mpr hoddRest
          have hupperRest : weight rest ≤ (Nat.fib rest.length : Int) - 1 := by
            simpa [upper, hrestNotEven] using hrestBounds.2
          have hoddRest2 : Odd (rest.length + 2) :=
            (odd_add_two_iff rest.length).2 hoddRest
          rw [weight_one_zero_cons, hoddRest2.neg_one_pow] at hnormalizedPositive
          have hmono : Nat.fib rest.length ≤ Nat.fib (rest.length + 2) :=
            Nat.fib_mono (by omega)
          omega

theorem even_length_of_head_one {digits : List Nat}
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1)
    (hpositive : 0 < weight digits) : Even digits.length := by
  have htrim := trimmed_even_of_pos hcanonical hpositive
  cases digits with
  | nil => simp at hhead
  | cons digit tail =>
      have hdigit : digit = 1 := by simpa using hhead
      subst digit
      simpa [trim] using htrim

private theorem succ_le_fib_two_mul_add_one : ∀ value : Nat,
    0 < value → value + 1 ≤ Nat.fib (2 * value + 1) := by
  intro value hvalue
  have hlinear := Nat.le_fib_add_one (value + 1)
  have hrec := Nat.fib_add_two (n := value)
  have hpos : 0 < Nat.fib value := Nat.fib_pos.2 hvalue
  have hnear : value + 1 ≤ Nat.fib (value + 2) := by omega
  exact hnear.trans (Nat.fib_mono (by omega))

/-- Every positive integer has a canonical representation whose deepest
occupied position has odd shallow depth. -/
theorem positive_representation (value : Nat) (hvalue : 0 < value) :
    ∃ digits : List Nat,
      Canonical digits ∧ digits ≠ [] ∧ digits.head? = some 1 ∧
        Even digits.length ∧ weight digits = value := by
  let n := 2 * value
  have hnEven : Even n := ⟨value, by omega⟩
  have hlower : lower n ≤ (value : Int) := by
    simp [lower, hnEven]
  have hupper : (value : Int) ≤ upper n := by
    simp only [upper, if_pos hnEven]
    have hsmall := succ_le_fib_two_mul_add_one value hvalue
    have hsmallInt : (value : Int) + 1 ≤ Nat.fib (2 * value + 1) := by
      exact_mod_cast hsmall
    dsimp [n]
    omega
  obtain ⟨digits, hlength, hcanonical, hweight⟩ :=
    represents_of_mem_interval n value hlower hupper
  let normalized := trim digits
  have hnormalizedCanonical : Canonical normalized := canonical_trim hcanonical
  have hnormalizedWeight : weight normalized = value := (weight_trim digits).trans hweight
  have hhead : normalized.head? = some 1 :=
    trim_head_one hcanonical (by rw [hweight]; exact_mod_cast hvalue.ne')
  have hnonempty : normalized ≠ [] := by intro h; rw [h] at hhead; simp at hhead
  have heven : Even normalized.length := by
    apply trimmed_even_of_pos hcanonical
    rw [hweight]
    exact_mod_cast hvalue
  exact ⟨normalized, hnormalizedCanonical, hnonempty, hhead, heven, hnormalizedWeight⟩

private theorem trimmed_odd_of_neg {digits : List Nat}
    (hcanonical : Canonical digits) (hnegative : weight digits < 0) :
    Odd (trim digits).length := by
  let normalized := trim digits
  have hnormalizedCanonical : Canonical normalized := canonical_trim hcanonical
  have hnormalizedWeight : weight normalized = weight digits := weight_trim digits
  have hhead : normalized.head? = some 1 :=
    trim_head_one hcanonical (by omega)
  have hnormalizedNegative : weight normalized < 0 := by
    rw [hnormalizedWeight]
    exact hnegative
  change Odd normalized.length
  cases hnorm : normalized with
  | nil => rw [hnorm] at hhead; simp at hhead
  | cons digit tail =>
      rw [hnorm] at hhead hnormalizedCanonical hnormalizedNegative
      have hdigit : digit = 1 := by simpa using hhead
      subst digit
      by_cases hodd : Odd (tail.length + 1)
      · simpa using hodd
      · exfalso
        have hevenLength : Even (tail.length + 1) := by
          by_contra heven
          exact hodd (Nat.not_even_iff_odd.mp heven)
        cases tail with
        | nil =>
          obtain ⟨k, hk⟩ := hevenLength
          norm_num at hk
          omega
        | cons next rest =>
          have hnext : next = 0 := hnormalizedCanonical.2.1 rfl
          subst next
          have hevenRest : Even rest.length := (even_add_two_iff rest.length).1 (by
            simpa only [List.length_cons] using hevenLength)
          have hrestBounds := mem_interval_of_represents rest.length (weight rest)
            ⟨rest, rfl, hnormalizedCanonical.2.2.2.2, rfl⟩
          have hlowerRest : -(Nat.fib rest.length : Int) ≤ weight rest := by
            simpa [lower, hevenRest] using hrestBounds.1
          have hevenRest2 : Even (rest.length + 2) :=
            (even_add_two_iff rest.length).2 hevenRest
          rw [weight_one_zero_cons, hevenRest2.neg_one_pow] at hnormalizedNegative
          have hrec := fib_add_two_int rest.length
          have hpos : 0 < Nat.fib (rest.length + 1) := Nat.fib_pos.2 (by omega)
          omega

theorem odd_length_of_head_one {digits : List Nat}
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1)
    (hnegative : weight digits < 0) : Odd digits.length := by
  have htrim := trimmed_odd_of_neg hcanonical hnegative
  cases digits with
  | nil => simp at hhead
  | cons digit tail =>
      have hdigit : digit = 1 := by simpa using hhead
      subst digit
      simpa [trim] using htrim

private theorem weight_ne_zero_of_head_one {digits : List Nat}
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1) :
    weight digits ≠ 0 := by
  cases digits with
  | nil => simp at hhead
  | cons digit tail =>
      have hdigit : digit = 1 := by simpa using hhead
      subst digit
      cases tail with
      | nil => norm_num [weight]
      | cons next rest =>
          have hnext : next = 0 := hcanonical.2.1 rfl
          subst next
          have hrestBounds := mem_interval_of_represents rest.length (weight rest)
            ⟨rest, rfl, hcanonical.2.2.2.2, rfl⟩
          by_cases heven : Even rest.length
          · have hlower : -(Nat.fib rest.length : Int) ≤ weight rest := by
              simpa [lower, heven] using hrestBounds.1
            have heven2 : Even (rest.length + 2) :=
              (even_add_two_iff rest.length).2 heven
            rw [weight_one_zero_cons, heven2.neg_one_pow]
            have hrec := fib_add_two_int rest.length
            have hpos : 0 < Nat.fib (rest.length + 1) := Nat.fib_pos.2 (by omega)
            omega
          · have hodd : Odd rest.length := Nat.not_even_iff_odd.mp heven
            have hupper : weight rest ≤ (Nat.fib rest.length : Int) - 1 := by
              simpa [upper, heven] using hrestBounds.2
            have hodd2 : Odd (rest.length + 2) :=
              (odd_add_two_iff rest.length).2 hodd
            rw [weight_one_zero_cons, hodd2.neg_one_pow]
            have hmono : Nat.fib rest.length ≤ Nat.fib (rest.length + 2) :=
              Nat.fib_mono (by omega)
            omega

theorem weight_pos_of_head_one_even {digits : List Nat}
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1)
    (heven : Even digits.length) : 0 < weight digits := by
  rcases lt_trichotomy (weight digits) 0 with hnegative | hzero | hpositive
  · have hodd := odd_length_of_head_one hcanonical hhead hnegative
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hodd
    omega
  · exact (weight_ne_zero_of_head_one hcanonical hhead hzero).elim
  · exact hpositive

theorem weight_neg_of_head_one_odd {digits : List Nat}
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1)
    (hodd : Odd digits.length) : weight digits < 0 := by
  rcases lt_trichotomy (weight digits) 0 with hnegative | hzero | hpositive
  · exact hnegative
  · exact (weight_ne_zero_of_head_one hcanonical hhead hzero).elim
  · have heven := even_length_of_head_one hcanonical hhead hpositive
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hodd
    omega

/-- Every positive integer has a canonical representation of its negative
whose deepest occupied position has even shallow depth. -/
theorem negative_representation (value : Nat) (hvalue : 0 < value) :
    ∃ digits : List Nat,
      Canonical digits ∧ digits ≠ [] ∧ digits.head? = some 1 ∧
        Odd digits.length ∧ weight digits = -(value : Int) := by
  let n := 2 * value + 1
  have hnOdd : Odd n := ⟨value, by omega⟩
  have hnNotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hnOdd
  have hlower : lower n ≤ -(value : Int) := by
    simp only [lower, if_neg hnNotEven]
    have hsmall := succ_le_fib_two_mul_add_one value hvalue
    have hmono : Nat.fib (2 * value + 1) ≤ Nat.fib (2 * value + 2) :=
      Nat.fib_mono (by omega)
    have hbound : value ≤ Nat.fib (2 * value + 2) := by omega
    exact_mod_cast (by omega : -(Nat.fib (2 * value + 2) : Int) ≤ -(value : Int))
  have hupper : -(value : Int) ≤ upper n := by
    simp only [upper, if_neg hnNotEven]
    have hpos : 0 < Nat.fib n := Nat.fib_pos.2 (by dsimp [n]; omega)
    omega
  obtain ⟨digits, hlength, hcanonical, hweight⟩ :=
    represents_of_mem_interval n (-(value : Int)) hlower hupper
  let normalized := trim digits
  have hnormalizedCanonical : Canonical normalized := canonical_trim hcanonical
  have hnormalizedWeight : weight normalized = -(value : Int) :=
    (weight_trim digits).trans hweight
  have hhead : normalized.head? = some 1 :=
    trim_head_one hcanonical (by rw [hweight]; exact neg_ne_zero.mpr (by exact_mod_cast hvalue.ne'))
  have hnonempty : normalized ≠ [] := by intro h; rw [h] at hhead; simp at hhead
  have hodd : Odd normalized.length := by
    apply trimmed_odd_of_neg hcanonical
    rw [hweight]
    exact neg_neg_of_pos (by exact_mod_cast hvalue)
  exact ⟨normalized, hnormalizedCanonical, hnonempty, hhead, hodd, hnormalizedWeight⟩

end D5.S1.Words.NegativeExpansions.NegaFibonacci
