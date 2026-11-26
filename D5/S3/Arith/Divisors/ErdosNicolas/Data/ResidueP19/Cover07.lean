/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked19,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked20,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked21,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked22,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked23,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked24,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked25,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked26,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked27,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked28,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked29,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked30,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover07.checked31
   digest: Finite numeric coverage checks for bounded prefix subtrees. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Terminals

/-! Each declaration checks a fixed prefix and its complete remaining exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover07

theorem checked19 :
    checkPrefixCover terminalPrefixes [5] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked19

theorem checked20 :
    checkPrefixCover terminalPrefixes [6] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked20

theorem checked21 :
    checkPrefixCover terminalPrefixes [7] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked21

theorem checked22 :
    checkPrefixCover terminalPrefixes [8] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked22

theorem checked23 :
    checkPrefixCover terminalPrefixes [9] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked23

theorem checked24 :
    checkPrefixCover terminalPrefixes [10] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked24

theorem checked25 :
    checkPrefixCover terminalPrefixes [11] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked25

theorem checked26 :
    checkPrefixCover terminalPrefixes [12] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked26

theorem checked27 :
    checkPrefixCover terminalPrefixes [13] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked27

theorem checked28 :
    checkPrefixCover terminalPrefixes [14] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked28

theorem checked29 :
    checkPrefixCover terminalPrefixes [15] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked29

theorem checked30 :
    checkPrefixCover terminalPrefixes [16] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked30

theorem checked31 :
    checkPrefixCover terminalPrefixes [17] [7, 4, 3, 2, 2, 1] = true := by
  decide +kernel

#print axioms checked31

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Cover07
