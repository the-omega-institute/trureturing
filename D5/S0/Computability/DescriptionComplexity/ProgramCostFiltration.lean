/- GID: D5/S0/Computability/DescriptionComplexity/ProgramCostFiltration
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/ProgramCostFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Description filters programs; runtime alone need not; mixed cost filters again. -/

import D5.S0.Asymptotics.FiniteProgramLevelSet
import Mathlib.Data.Nat.Log

namespace D5.S0.Computability.DescriptionComplexity.ProgramCostFiltration

open D5.S0.Asymptotics.FiniteProgramLevelSet

/-- Injective binary descriptions have finite length sublevels. A uniformly
bounded compiler for constant functions makes a runtime sublevel infinite,
while adding logarithmic runtime to description length restores finiteness. -/
theorem program_cost_filtration_classification
    {Program Data : Type*} [Infinite Data]
    (Q T : Nat)
    (code : Program -> BinaryProgram)
    (codeInjective : Function.Injective code)
    (semantics : Program -> Data -> Data)
    (runtime : Program -> Nat)
    (constantProgram : Data -> Program)
    (constantCorrect : forall value input,
      semantics (constantProgram value) input = value)
    (constantTime : forall value, runtime (constantProgram value) <= T) :
    Set.Finite {program | (code program).length <= Q} /\
      Set.Infinite {function : Data -> Data |
        exists program, semantics program = function /\ runtime program <= T} /\
      Set.Finite {program |
        (code program).length + Nat.log 2 (runtime program) <= Q} := by
  have finiteLength : Set.Finite {program | (code program).length <= Q} := by
    simpa [boundedPrograms] using
      (bounded_programs_finite Q).preimage codeInjective.injOn
  refine ⟨finiteLength, ?_, ?_⟩
  · have constantFunctionInjective :
        Function.Injective (fun value : Data => Function.const Data value) := by
      intro left right equalFunctions
      let input : Data := Classical.choice (Infinite.nonempty Data)
      exact congrFun equalFunctions input
    apply (Set.infinite_range_of_injective constantFunctionInjective).mono
    rintro function ⟨value, rfl⟩
    refine ⟨constantProgram value, ?_, constantTime value⟩
    funext input
    exact constantCorrect value input
  · apply finiteLength.subset
    intro program mixedBound
    change (code program).length <= Q
    change (code program).length + Nat.log 2 (runtime program) <= Q at mixedBound
    omega

#print axioms program_cost_filtration_classification

end D5.S0.Computability.DescriptionComplexity.ProgramCostFiltration
