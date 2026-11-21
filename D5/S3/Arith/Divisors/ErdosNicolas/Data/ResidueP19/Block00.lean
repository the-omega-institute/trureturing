/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block00
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block00.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block00

def certificates : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 2, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 1, 0], .kernel, 112894026876⟩,
    ⟨[0, 0, 0, 0, 1, 1, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 2, 0], .kernel, 177221957974⟩,
    ⟨[0, 0, 0, 0, 1, 2, 1], .prefix, 364144975506⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 2, 0, 1], .prefix, 180825643970⟩,
    ⟨[0, 0, 0, 0, 2, 1], .prefix, 180825643970⟩,
    ⟨[0, 0, 0, 0, 2, 2], .prefix, 222608749078⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 0, 1, 0], .kernel, 122595086434⟩,
    ⟨[0, 0, 0, 1, 0, 1, 1], .kernel, 198424259395⟩,
    ⟨[0, 0, 0, 1, 0, 2, 0], .kernel, 176603243038⟩,
    ⟨[0, 0, 0, 1, 0, 2, 1], .prefix, 364144975506⟩,
    ⟨[0, 0, 0, 1, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 1, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 1, 1, 0], .kernel, 235489113310⟩,
    ⟨[0, 0, 0, 1, 1, 1, 1], .prefix, 466529274077⟩,
    ⟨[0, 0, 0, 1, 1, 2], .prefix, 353825201012⟩,
    ⟨[0, 0, 0, 1, 2, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 2, 0, 1], .prefix, 361651287940⟩,
    ⟨[0, 0, 0, 1, 2, 1], .prefix, 361651287940⟩,
    ⟨[0, 0, 0, 1, 2, 2], .prefix, 445217498156⟩,
    ⟨[0, 0, 0, 2, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 2, 0, 0, 1], .prefix, 180825643970⟩,
    ⟨[0, 0, 0, 2, 0, 1], .prefix, 180825643970⟩,
    ⟨[0, 0, 0, 2, 0, 2], .prefix, 222608749078⟩,
    ⟨[0, 0, 0, 2, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 2, 1, 0, 1], .prefix, 361651287940⟩,
    ⟨[0, 0, 0, 2, 1, 1], .prefix, 361651287940⟩,
    ⟨[0, 0, 0, 2, 1, 2], .prefix, 445217498156⟩,
    ⟨[0, 0, 0, 2, 2, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 2, 2, 0, 1], .prefix, 542476931910⟩,
    ⟨[0, 0, 0, 2, 2, 1], .prefix, 542476931910⟩,
    ⟨[0, 0, 0, 2, 2, 2], .prefix, 667826247234⟩,
    ⟨[0, 0, 0, 3, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 3, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 3, 0, 1, 0], .kernel, 235489113310⟩,
    ⟨[0, 0, 0, 3, 0, 1, 1], .prefix, 466529274077⟩,
    ⟨[0, 0, 0, 3, 0, 2], .prefix, 353825201012⟩,
    ⟨[0, 0, 0, 3, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 3, 1, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 3, 1, 1, 0], .kernel, 399179861882⟩,
    ⟨[0, 0, 0, 3, 1, 1, 1], .prefix, 916042137628⟩,
    ⟨[0, 0, 0, 3, 1, 2], .prefix, 632140515688⟩,
    ⟨[0, 0, 0, 3, 2, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 3, 2, 0, 1], .prefix, 723302575880⟩,
    ⟨[0, 0, 0, 3, 2, 1], .prefix, 723302575880⟩,
    ⟨[0, 0, 0, 3, 2, 2], .prefix, 890434996312⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 1, 0], .kernel, 117960851971⟩,
    ⟨[0, 0, 1, 0, 0, 1, 1], .prefix, 212537673696⟩,
    ⟨[0, 0, 1, 0, 0, 2], .prefix, 184186693145⟩,
    ⟨[0, 0, 1, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 1, 0, 1], .kernel, 237327344766⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block00
