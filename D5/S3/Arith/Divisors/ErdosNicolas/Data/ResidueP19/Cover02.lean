/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover02
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover02.checked3,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover02.checked4,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover02.checked5,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover02.checked6,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover02.checked7
   digest: Finite numeric coverage checks for bounded prefix subtrees. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Terminals

/-! Each declaration checks a fixed prefix and its complete remaining exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover02

theorem checked3 :
    checkPrefixCover terminalPrefixes [0, 3] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked3

theorem checked4 :
    checkPrefixCover terminalPrefixes [0, 4] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked4

theorem checked5 :
    checkPrefixCover terminalPrefixes [0, 5] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked5

theorem checked6 :
    checkPrefixCover terminalPrefixes [0, 6] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked6

theorem checked7 :
    checkPrefixCover terminalPrefixes [0, 7] [4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked7

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover02
