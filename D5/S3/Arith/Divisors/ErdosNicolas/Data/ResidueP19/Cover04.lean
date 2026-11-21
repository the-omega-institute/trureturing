/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover04
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover04.checked11,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover04.checked12,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover04.checked13,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover04.checked14,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover04.checked15
   digest: Finite numeric coverage checks for bounded prefix subtrees. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Terminals

/-! Each declaration checks a fixed prefix and its complete remaining exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover04

theorem checked11 :
    checkPrefixCover terminalPrefixes [1, 3] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked11

theorem checked12 :
    checkPrefixCover terminalPrefixes [1, 4] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked12

theorem checked13 :
    checkPrefixCover terminalPrefixes [1, 5] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked13

theorem checked14 :
    checkPrefixCover terminalPrefixes [1, 6] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked14

theorem checked15 :
    checkPrefixCover terminalPrefixes [1, 7] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked15

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover04
