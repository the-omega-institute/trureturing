/- GID: D5/S1/Words/Palindromes/FridPrefix/NumeralSemantics
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/NumeralSemantics
   mirror-E: none(waiver:canonical-order-semantics)
   anchors: []
   utility: none
   digest: Equal-width canonical Fibonacci digit values have exactly lexicographic order. -/

/-
proof_shape: content (canonical_lex_value).
escape_witness: induction on the first differing canonical digit with a strict tail bound.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S0/Automata/BinaryZeckendorfLanguage; module statement_id sha256:87b15f790efca613794d25fe2bc822ee2420eb2ab847760e509a3059c25a8f17
    D5/S0/Automata/BinaryZeckendorfLanguage.NoAdjacentOnes: sha256:5f646bb806cb8cd8c7f639908d761f070355bdbbfede407d3acc033120cb2fce
  D5/S1/Digit/GoldenBase4IntervalMachine; module statement_id sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
    D5/S1/Digit/GoldenBase4IntervalMachine.fibPair: sha256:cbaa673b2d8bdcd2f56ac60fbd4b8496a29d1b3a9a6aa673af463265b40f3053
  D5/S1/Digit/ZeckendorfRawWindow; module statement_id sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
    D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates: sha256:deeba6dbde4255f8972f23006c02b555aa13a8eb176d45ddc52b66429d5fc2b2
    D5/S1/Digit/ZeckendorfRawWindow.support: sha256:6e85f7358067b00dc6b9dd199d81bc985b8e710bf1a0136ac0450f0c136dec49
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Digit.ZeckendorfRawWindow

namespace D5.S1.Words.FridPrefix

open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S0.Automata.BinaryZeckendorfLanguage

/-- The numeric order and the first-differing-digit order agree, including common zero padding. -/
theorem canonical_lex_value (u v : List (Fin 2)) (hu : NoAdjacentOnes u)
    (hv : NoAdjacentOnes v) (hl : u.length=v.length) :
    (fibPair u).1 < (fibPair v).1 ↔ List.Lex (· < ·) u v := by
  have bound (w : List (Fin 2)) (hw : NoAdjacentOnes w) :
      (fibPair w).1 < Nat.fib (w.length+2) := by
    have hs := source_word_coordinates w hw
    rw [← hs.2.2.1]
    apply hs.1.sum_fib_lt
    intro a ha
    have hm := List.mem_of_mem_head? ha
    rcases List.mem_append.mp hm with hm | hm
    · exact hs.2.1 a hm
    · simp only [List.mem_singleton] at hm
      omega
  induction u generalizing v with
  | nil =>
    have he : v=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst v
    simp
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v =>
      have hu' : NoAdjacentOnes u := hu.tail
      have hv' : NoAdjacentOnes v := hv.tail
      have hl' : u.length=v.length := by simpa using hl
      have hb₁ := bound u hu'
      have hb₂ := bound v hv'
      fin_cases a <;> fin_cases b
      · simpa only [fibPair, Fin.val_zero, zero_mul, zero_add, List.lex_cons_iff]
          using ih v hu' hv' hl'
      · constructor
        · intro _
          exact List.Lex.rel (by decide)
        · intro _
          simp only [fibPair, Fin.val_zero, Fin.val_one, zero_mul, zero_add, one_mul]
          rw [← hl']
          omega
      · constructor
        · intro hn
          simp only [fibPair, Fin.val_zero, Fin.val_one, zero_mul, zero_add, one_mul] at hn
          rw [hl'] at hn
          omega
        · intro hn
          cases hn with
          | rel h => norm_num at h
      · simp only [fibPair, Fin.val_one, one_mul, List.lex_cons_iff]
        rw [hl']
        simpa only [Nat.add_lt_add_iff_left] using ih v hu' hv' hl'

end D5.S1.Words.FridPrefix
