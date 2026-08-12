/- GID: D5/S0/Computability/TotalOrbitEvaluator
   generality: G
   mirror-B: D5/B/S0/Computability/TotalOrbitEvaluator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No computable total function evaluates every partial-recursive code at every input. -/

import Mathlib.Computability.PartrecCode

namespace D5.S0.Computability.TotalOrbitEvaluator

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- No computable total function returns the value of every partial-recursive
code at every input. The contradiction uses the library's binary fixed-point
theorem with successor as a computable fixed-point-free output map. -/
theorem no_computable_total_orbit_evaluator :
    Not (Exists fun evaluator : Code -> Nat -> Nat =>
      Computable₂ evaluator /\
      forall code input, eval code input = Part.some (evaluator code input)) := by
  rintro ⟨evaluator, hComputable, hEvaluates⟩
  let diagonal : Code -> Nat -> Part Nat :=
    fun code input => Part.some (evaluator code input + 1)
  have hDiagonal : Partrec₂ diagonal := by
    exact (Computable.succ.comp₂ hComputable).partrec₂
  obtain ⟨fixedCode, hFixed⟩ := Nat.Partrec.Code.fixed_point₂ hDiagonal
  have hAtZero := congrFun hFixed 0
  rw [hEvaluates fixedCode 0] at hAtZero
  simp [diagonal] at hAtZero

/-- The domain of partial-recursive program codes is inhabited. -/
example : Nonempty Code := inferInstance

/-- The total evaluator function type ruled out by the theorem's full
conjunction is itself inhabited. -/
example : Nonempty (Code -> Nat -> Nat) := ⟨fun _ _ => 0⟩

end D5.S0.Computability.TotalOrbitEvaluator
