/- GID: D5/S0/Asymptotics/FiniteProgramLevelSet
   generality: G
   mirror-B: D5/B/S0/Asymptotics/FiniteProgramLevelSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The programs over a finite alphabet with length at most a fixed budget form a finite level set; this closes clause (a) only. Clauses (b) and (c) remain unresolved. -/

import Mathlib.Data.Set.Finite.List

namespace D5.S0.Asymptotics.FiniteProgramLevelSet

abbrev BinaryProgram := List (Fin 2)

/-- Binary algorithm programs whose description length fits within a budget. -/
def boundedPrograms (Q : Nat) : Set BinaryProgram :=
  {program | program.length ≤ Q}

/-- The finite-level-set clause: a finite alphabet and a fixed length budget
give only finitely many binary programs. -/
theorem bounded_programs_finite (Q : Nat) : (boundedPrograms Q).Finite := by
  exact List.finite_length_le (Fin 2) Q

end D5.S0.Asymptotics.FiniteProgramLevelSet
