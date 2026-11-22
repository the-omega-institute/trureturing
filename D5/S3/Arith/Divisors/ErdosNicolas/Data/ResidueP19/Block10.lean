/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block10
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block10.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block10

def certificates : List ResidueTerminal :=
  [
    ⟨[10, 2], .prefix, 914110245559⟩,
    ⟨[10, 3], .prefix, 1172653425295⟩,
    ⟨[10, 4], .prefix, 1441254290238⟩,
    ⟨[10, 5], .prefix, 1699797469974⟩,
    ⟨[10, 6], .prefix, 1948888380199⟩,
    ⟨[10, 7], .prefix, 2201935830341⟩,
    ⟨[11], .prefix, 359922431200⟩,
    ⟨[12], .prefix, 370399186887⟩,
    ⟨[13], .prefix, 395856861858⟩,
    ⟨[14], .prefix, 408664261627⟩,
    ⟨[15], .prefix, 421065837717⟩,
    ⟨[16], .prefix, 435146422774⟩,
    ⟨[17], .prefix, 445217498156⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block10
