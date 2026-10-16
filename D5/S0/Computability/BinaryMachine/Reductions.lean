/- GID: D5/S0/Computability/BinaryMachine/Reductions
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Reductions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine Reductions supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/Reductions.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.Composition

/-!
Many-one reductions compose through actual polynomial-time transducers. The
hardness transfer theorems quantify over the original machine-based NP class.
-/

@[expose] public section

namespace Complexity

/-- Transitivity of polynomial-time many-one reductions. -/
theorem PolyRed.trans {A B C : Language} (hAB : PolyRed A B) (hBC : PolyRed B C) :
    PolyRed A C := by
  obtain ⟨f, hf, hAB⟩ := hAB
  obtain ⟨g, hg, hBC⟩ := hBC
  exact ⟨fun input => g (f input), polyTime_comp (f := f) (g := g) hg hf,
    fun input => (hAB input).trans (hBC (f input))⟩

theorem polyRed_trans {A B C : Language} (hAB : PolyRed A B) (hBC : PolyRed B C) :
    PolyRed A C := hAB.trans hBC

/-- Reduce a known NP-hard language to the target. -/
theorem NPHard.of_reduction {A B : Language} (hA : NPHard A) (hAB : PolyRed A B) :
    NPHard B := by
  intro L hL
  exact (hA L hL).trans hAB

/-- NP membership plus a reduction from any NP-hard language gives completeness. -/
theorem NPComplete.of_reduction {A B : Language} (hA : NPHard A)
    (hAB : PolyRed A B) (hB : InNP B) : NPComplete B :=
  ⟨hB, hA.of_reduction hAB⟩

theorem NPComplete.npHard {L : Language} (hL : NPComplete L) : NPHard L := hL.2

theorem NPComplete.inNP {L : Language} (hL : NPComplete L) : InNP L := hL.1

/-- Transfer completeness along a polynomial reduction, when the destination's
NP verifier has separately been established. -/
theorem NPComplete.transfer {A B : Language} (hA : NPComplete A)
    (hAB : PolyRed A B) (hB : InNP B) : NPComplete B :=
  NPComplete.of_reduction hA.2 hAB hB

end Complexity
