/- GID: D5/S0/Computability/BinaryMachine/DecisionComposition
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/DecisionComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial preprocessing preserves both Boolean decisions of a total verifier. -/

import D5.S0.Computability.BinaryMachine.DecisionSimulation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.DecisionComposition
open StackProgram

def program (pre verifier : Machine) :=
  seq (TransducerPair.normalized pre) (DecisionSimulation.program verifier)
def encoding (pre verifier : Machine) :=
  (TapeToStacks.normalEncoding pre).sum (DecisionSimulation.encoding verifier)

/-- Polynomial preprocessing is followed by the complete accepting or rejecting
run of the given machine, with no assumption that the verifier accepts. -/
theorem preprocess {f : Word → Word} (hf : PolyTime f) (M : Machine)
    (hM : PolynomialTimeMachine M) :
    ∃ N : Machine, PolynomialTimeMachine N ∧ ∀ x, Accepts N x ↔ Accepts M (f x) := by
  obtain ⟨pre, c, k, hpre⟩ := hf
  obtain ⟨d, l, hM⟩ := hM
  let bound := fun n => 72 * (n + powerBound c k n +
    powerBound d l (n + 2 * powerBound c k n) + 1)
  have hb : PolynomialBound bound := polynomialBound_compositionBound c k d l
  let S := compile (program pre M) (encoding pre M)
  have hruns : ∀ x, ∃ time decision registers,
      time ≤ bound x.length ∧ StackMachine.runInput S time x = some (decision, registers) ∧
      (decision = true ↔ Accepts M (f x)) := by
    intro x
    obtain ⟨t, middle, ht, hp, hout⟩ := hpre x
    obtain ⟨s, decision, out, hs, hv⟩ := hM middle.output
    obtain ⟨u, hu, he⟩ := TransducerPair.exec_normalized pre t x middle hp (StackPair.initial x)
      (by simp [StackPair.initial, StackPair.input]) (by simp [StackPair.initial, StackPair.input])
      (by simp [StackPair.initial, StackPair.input])
    let r := StackMachine.set (StackPair.initial x) 0 middle.output
    obtain ⟨v, registers, hvt, he'⟩ := DecisionSimulation.exec_program M s middle.output decision out hv r
      (by simp [r]) (by simp [r, StackPair.initial, StackPair.input])
      (by simp [r, StackPair.initial, StackPair.input])
    have hh := exec_seq _ _ he he'
    have hlen := runInput_output_length_le pre t x (true, middle) hp
    change middle.output.length ≤ x.length + 2 * t at hlen
    have hs' := powerBound_mono d l (by omega : middle.output.length ≤ x.length + 2 * powerBound c k x.length)
    refine ⟨u + v, decision, registers, ?_, ?_, ?_⟩
    · unfold bound; omega
    · exact compile_exec (encoding pre M) hh
    · constructor
      · intro hd
        subst decision
        exact ⟨s, out, by simpa [hout] using hv⟩
      · intro ⟨s', out', hv'⟩
        have heq := run_deterministic M (initial M middle.output) hv
          (by simpa [runInput, ← hout] using hv')
        exact congrArg Prod.fst heq
  have htotal := StackCompile.polynomialTimeMachine_of_stack S bound hb
    (fun x => by obtain ⟨t, b, r, ht, he, _⟩ := hruns x; exact ⟨t, b, r, ht, he⟩)
  refine ⟨StackCompile.compile S, htotal, ?_⟩
  intro x
  obtain ⟨t, b, r, ht, he, hb⟩ := hruns x
  have ha := StackCompile.accepts_iff S x ⟨t, b, r, he⟩
  constructor
  · intro hx
    obtain ⟨s, out, hs⟩ := ha.mp hx
    have heq := StackMachine.run_deterministic S (StackMachine.initial S x) hs he
    exact hb.mp (congrArg Prod.fst heq).symm
  · intro hx
    have htrue := hb.mpr hx
    subst b
    exact ha.mpr ⟨t, r, he⟩

end Complexity.DecisionComposition
