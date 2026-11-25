/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/MainRank3530Part03
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/MainRank3530Part03.chunk_checked
   digest: Kernel-checked exact sum of a consecutive interval of original rank rows. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Inputs

/-! Opaque checks retain the exact original indexed-rank computation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.MainRank3530Part03

open MainRank3530Inputs

/-- Every original row in this interval is evaluated with its unchanged global indices. -/
theorem chunk_checked :
    rankIndexRange mainScale 1 count readout 1536 512 = 3159348692 := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.MainRank3530Part03
