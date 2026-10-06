/- GID: D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/LanguageMonitor
   mirror-E: none(waiver:paired-digit-language-semantics)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity.palindrome_endpoint; instance=D5/S1/Words/Palindromes/FridPrefix/LanguageData.certificate
   digest: A finite monitor separates mismatch and endpoint languages for all valid words. -/

/-
proof_shape: content (every_word).
escape_witness: all-word induction using the concrete closed monitor.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.LanguageData
import D5.S1.Words.Palindromes.FridPrefix.MaskReachability

namespace D5.S1.Words.FridPrefix.Language

def initial : Signature :=
  ⟨badStart, endpointStart, 0, 0, false, true⟩

def invalid : Signature := ⟨0,0,0,0,false,false⟩

def step (s : Signature) (symbol : Fin 4) : Signature :=
  let x := symbol.val / 2
  let y := symbol.val % 2
  if !s.valid || (s.previousX = 1 && x = 1) ||
      (s.previousY = 1 && y = 1) || (!s.strict && decide (y < x)) then
    invalid
  else
    ⟨maskStep badRows s.bad symbol.val,
     maskStep endpointMasks s.endpoint symbol.val,
     x, y, s.strict || decide (x < y), true⟩

def hasAccept (mask accept : ℕ) : Bool := (mask &&& accept) != 0

def conclusion (s : Signature) : Prop :=
  s.valid = true → s.strict = true →
    hasAccept s.bad badAccept = !hasAccept s.endpoint endpointAccept

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- The exact monitor separates reflected mismatches from endpoint acceptance on every word. -/
theorem every_word (w : List (Fin 4)) :
    conclusion (w.foldl step initial) := by
  have initial_mem : initial ∈ certificate := by decide +kernel
  have finite_closed : ∀ i : Fin certificate.length, ∀ symbol : Fin 4,
      step (certificate.get i) symbol ∈ certificate := by decide +kernel
  have finite_terminal : ∀ i : Fin certificate.length, conclusion (certificate.get i) := by
    unfold conclusion
    decide +kernel

  have h : ∀ s ∈ certificate, ∀ v : List (Fin 4), v.foldl step s ∈ certificate := by
    intro s hs v
    induction v generalizing s with
    | nil => simpa using hs
    | cons symbol v ih =>
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hs
        have hc : step s symbol ∈ certificate := by
          rw [← hi]
          exact finite_closed i symbol
        simpa only [List.foldl_cons] using ih (step s symbol) hc
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (h initial initial_mem w)
  rw [← hi]
  exact finite_terminal i

end D5.S1.Words.FridPrefix.Language
