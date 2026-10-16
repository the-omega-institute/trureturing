/- GID: D5/S0/Computability/BinaryMachine/WitnessBudget
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/WitnessBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original target certificate bounds are enforced by a total finite stack computation. -/

import D5.S0.Computability.BinaryMachine.StackPower
import D5.S0.Computability.BinaryMachine.StackCompare
import D5.S0.Computability.BinaryMachine.StackPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.WitnessBudget
open StackMachine (Registers)
open StackProgram

def test (c e : Nat) := seq (StackWords.length (k := 6) 0 2 6)
  (seq (push (k := 6) 2 true) (seq (StackPower.power c e) (StackCompare.check (k := 6) 1 3)))

def encoding (c e : Nat) := StackWords.copyMapEncoding.sum
  (Encoding.bool.sum ((StackPower.encoding c e).sum (Encoding.fin 3)))

/-- The target witness bound uses the actual target word length. Every target
and witness is covered, including coefficient zero, exponent zero and empties.
The input word is preserved; scratch registers are restored. -/
theorem exec_test (c e : Nat) (x w : Word) :
    ∃ t out, t ≤ 5 * x.length + StackPower.time c e (x.length + 1) + 2 * w.length + 11 ∧
      Exec (test c e) (test c e).start (StackPair.unpacked x w) t
        (decide (w.length ≤ powerBound c e x.length), out) ∧
      out 0 = x ∧ out 2 = List.replicate (x.length + 1) true ∧
      out 4 = [] ∧ out 5 = [] ∧ out 6 = [] ∧
      (out 3).length ≤ x.length + 3 * w.length + powerBound c e x.length + 4 := by
  let r := StackPair.unpacked x w
  let r₁ := StackMachine.set r 2 (List.replicate x.length true)
  let r₂ := StackMachine.set r₁ 2 (true :: r₁ 2)
  let r₃ := StackMachine.set r₂ 3 (List.replicate (c * (x.length + 1) ^ e) true)
  have h₁ := StackWords.exec_length (k := 6) 0 2 6 (by decide) (by decide) (by decide) r (by rfl)
  have h₁' : Exec (StackWords.length (k := 6) 0 2 6) (StackWords.length (k := 6) 0 2 6).start r
      (5 * x.length + 6) (true, r₁) := by
    simpa [r, StackPair.unpacked, StackPair.input, StackPair.certificate,
      StackWords.length, StackWords.copyMap, StackWords.clear, seq] using h₁
  have h₂ := exec_push (k := 6) 2 true r₁
  have h₃ := StackPower.exec_power c e (x.length + 1) r₂
    (by simp [r₂, r₁, List.replicate_succ])
    (by simp [r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate])
    (by simp [r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate])
    (by simp [r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate])
    (by simp [r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate])
  obtain ⟨s, out, hs, h₄, hf⟩ := StackCompare.exec_check (k := 6) 1 3 (by decide) r₃
  have h₄' : Exec (StackCompare.check (k := 6) 1 3) (StackCompare.check (k := 6) 1 3).start r₃ s
      (decide (w.length ≤ powerBound c e x.length), out) := by
    simpa [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate, powerBound_eq] using h₄
  have hh := exec_seq _ _ h₁' (exec_seq _ _ h₂ (exec_seq _ _ h₃ h₄'))
  have hs' : s ≤ 2 * w.length + 3 := by
    simpa [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate] using hs
  have hsize : ∀ j, (r₃ j).length ≤ x.length + w.length + powerBound c e x.length + 1 := by
    intro j
    by_cases hj₃ : j = 3
    · subst j; simp [r₃, powerBound_eq]; omega
    · by_cases hj₂ : j = 2
      · subst j; simp [r₃, r₂, r₁]; omega
      · by_cases hj₀ : j = 0
        · subst j; simp [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input]; omega
        · by_cases hj₁ : j = 1
          · subst j
            simp [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate]; omega
          · simp [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate,
              StackMachine.set, hj₃, hj₂, hj₀, hj₁]
  have hlength := StackMachine.run_length_le (compile (StackCompare.check (k := 6) 1 3) (Encoding.fin 3))
    s ⟨0, r₃⟩ (decide (w.length ≤ powerBound c e x.length), out)
    (compile_exec (Encoding.fin 3) h₄') (x.length + w.length + powerBound c e x.length + 1) hsize 3
  refine ⟨5 * x.length + 6 + (2 + (StackPower.time c e (x.length + 1) + s)), out, by omega, hh, ?_⟩
  have ho₀ := hf 0 (by decide) (by decide)
  have ho₂ := hf 2 (by decide) (by decide)
  have ho₄ := hf 4 (by decide) (by decide)
  have ho₅ := hf 5 (by decide) (by decide)
  have ho₆ := hf 6 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, by dsimp at hlength; omega⟩
  · simpa [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input] using ho₀
  · simpa [r₃, r₂, r₁, List.replicate_succ] using ho₂
  · simpa [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate] using ho₄
  · simpa [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate] using ho₅
  · simpa [r₃, r₂, r₁, r, StackPair.unpacked, StackPair.input, StackPair.certificate] using ho₆

end Complexity.WitnessBudget
