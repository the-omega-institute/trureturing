/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19.residue_step
   digest: Complete residue-tree certificate for largest prime nineteen. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover

/-! Opaque block and coverage proofs are composed without repeating their arithmetic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19

private theorem all_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append,
    Block00.chunk_checked, Block01.chunk_checked, Block02.chunk_checked, Block03.chunk_checked,
    Block04.chunk_checked, Block05.chunk_checked, Block06.chunk_checked, Block07.chunk_checked,
    Block08.chunk_checked, Block09.chunk_checked, Block10.chunk_checked, Bool.and_self]

private theorem chunk_checked :
    checkResidueTree 19 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 19,
      hHat (residueBoxValue 19 v / 19) ≤ ((residueBoxValue 19 v / 19).divisors.card : ℚ) →
      hHat (residueBoxValue 19 v) < ((residueBoxValue 19 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19
