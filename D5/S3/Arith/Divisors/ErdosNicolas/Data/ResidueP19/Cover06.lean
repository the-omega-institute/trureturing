/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover06
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover06.checked17,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover06.checked18
   digest: Finite numeric coverage checks for bounded prefix subtrees. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Terminals

/-! Each declaration checks a fixed prefix and its complete remaining exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover06

theorem checked17 :
    checkPrefixCover terminalPrefixes [3] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked17

theorem checked18 :
    checkPrefixCover terminalPrefixes [4] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked18

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover06
