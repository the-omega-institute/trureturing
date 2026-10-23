/- GID: D5/S0/Computability/BinaryMachine/Composition
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Composition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine Composition supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/Composition.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.TapeToStacks
public import D5.S0.Computability.BinaryMachine.PolynomialBound
public import D5.S0.Computability.BinaryMachine.StackCompile
import Lean.Elab.Tactic.Omega

/-!
Composition starts from two arbitrary tape transducers. Their outputs may have
unrelated work data nearby. The intermediate stack computation explicitly
extracts the contiguous binary result and empties its work registers before
starting the second simulation.
-/

@[expose] public section

namespace Complexity

set_option backward.isDefEq.respectTransparency false

/-- A polynomial bound on the three-stack implementation of two sequential tape
computations, after bounding the intermediate word by the first run's space. -/
def compositionBound (c k d l : Nat) (n : Nat) : Nat :=
  72 * (n + powerBound c k n + powerBound d l (n + 2 * powerBound c k n) + 1)

theorem polynomialBound_compositionBound (c k d l : Nat) :
    PolynomialBound (compositionBound c k d l) := by
  have hf := PolynomialBound.power c k
  have hmiddle := PolynomialBound.identity.add ((PolynomialBound.constant 2).mul hf)
  have hg := (PolynomialBound.power d l).comp hmiddle
  exact (PolynomialBound.constant 72).mul
    (((PolynomialBound.identity.add hf).add hg).add (PolynomialBound.constant 1))

/-- The intermediate machine here is fully compiled to a finite Boolean-stack
controller. Its time is counted primitive instructions, and every work register
is empty when a normalized simulated transducer returns. -/
theorem polyTime_composition_stack {f g : Word → Word} (hf : PolyTime f) (hg : PolyTime g) :
    ∃ S : StackMachine.Machine, ∃ bound : Nat → Nat,
      PolynomialBound bound ∧ ∀ input,
        ∃ time registers,
          time ≤ bound input.length ∧
          StackMachine.runInput S time input = some (true, registers) ∧
          registers 0 = g (f input) := by
  obtain ⟨first, c, k, hf⟩ := hf
  obtain ⟨second, d, l, hg⟩ := hg
  refine ⟨TapeToStacks.compositionMachine first second, compositionBound c k d l,
    polynomialBound_compositionBound c k d l, ?_⟩
  intro input
  obtain ⟨t, middle, ht, hfirst, hmiddle⟩ := hf input
  obtain ⟨s, out, hs, hsecond, hout⟩ := hg middle.output
  obtain ⟨time, htime, hrun⟩ :=
    TapeToStacks.run_compositionMachine first second t s input middle out hfirst hsecond
  have hlength := runInput_output_length_le first t input (true, middle) hfirst
  simp only at hlength
  have hmiddleBound : middle.output.length ≤ input.length + 2 * powerBound c k input.length := by omega
  have hs' := Nat.le_trans hs (powerBound_mono d l hmiddleBound)
  refine ⟨time, TapeToStacks.regs out.output [] [], ?_, hrun, ?_⟩
  · unfold compositionBound
    omega
  · simpa only [TapeToStacks.regs_zero, hmiddle] using hout

/-- Polynomial-time transducers are closed under composition. This includes the
actual tape cleanup needed between machines with arbitrary final work data. -/
theorem polyTime_comp {f g : Word → Word} (hg : PolyTime g) (hf : PolyTime f) :
    PolyTime (fun input => g (f input)) := by
  obtain ⟨S, bound, hbound, hS⟩ := polyTime_composition_stack hf hg
  exact StackCompile.polyTime_of_stack S bound hbound hS

theorem PolyTime.comp {f g : Word → Word} (hg : PolyTime g) (hf : PolyTime f) :
    PolyTime (g ∘ f) := polyTime_comp (f := f) (g := g) hg hf

end Complexity
