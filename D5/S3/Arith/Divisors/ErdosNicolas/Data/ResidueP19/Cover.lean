/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover.coverage_checked
   digest: Complete bounded exponent coverage assembled from opaque prefix checks. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block03
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block04
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block05
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block06
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block07
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block08
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block09
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Block10
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover03
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover04
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover05
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover06
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Cover07

/-! Only logical child composition is performed in this module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19

def certificates : List ResidueTerminal :=
  Block00.certificates ++ Block01.certificates ++ Block02.certificates ++ Block03.certificates ++
  Block04.certificates ++ Block05.certificates ++ Block06.certificates ++ Block07.certificates ++
  Block08.certificates ++ Block09.certificates ++ Block10.certificates

private theorem prefixes_eq :
    certificates.map ResidueTerminal.exponents = terminalPrefixes := by rfl

private theorem children0_checked :
    checkPrefixCover terminalPrefixes [0] [7, 4, 3, 2, 2, 1] = true := by
  apply checkPrefixCover_of_children
  apply List.all_eq_true.mpr
  intro e he
  have he' : e < 8 := List.mem_range.mp he
  interval_cases e
  · exact Cover00.checked0
  · exact Cover01.checked1
  · exact Cover01.checked2
  · exact Cover02.checked3
  · exact Cover02.checked4
  · exact Cover02.checked5
  · exact Cover02.checked6
  · exact Cover02.checked7

private theorem children1_checked :
    checkPrefixCover terminalPrefixes [1] [7, 4, 3, 2, 2, 1] = true := by
  apply checkPrefixCover_of_children
  apply List.all_eq_true.mpr
  intro e he
  have he' : e < 8 := List.mem_range.mp he
  interval_cases e
  · exact Cover03.checked8
  · exact Cover03.checked9
  · exact Cover03.checked10
  · exact Cover04.checked11
  · exact Cover04.checked12
  · exact Cover04.checked13
  · exact Cover04.checked14
  · exact Cover04.checked15

theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 19) =
      true := by
  rw [prefixes_eq]
  change checkPrefixCover terminalPrefixes [] [17, 7, 4, 3, 2, 2, 1] = true
  apply checkPrefixCover_of_children
  apply List.all_eq_true.mpr
  intro e he
  have he' : e < 18 := List.mem_range.mp he
  interval_cases e
  · exact children0_checked
  · exact children1_checked
  · exact Cover05.checked16
  · exact Cover06.checked17
  · exact Cover06.checked18
  · exact Cover07.checked19
  · exact Cover07.checked20
  · exact Cover07.checked21
  · exact Cover07.checked22
  · exact Cover07.checked23
  · exact Cover07.checked24
  · exact Cover07.checked25
  · exact Cover07.checked26
  · exact Cover07.checked27
  · exact Cover07.checked28
  · exact Cover07.checked29
  · exact Cover07.checked30
  · exact Cover07.checked31

#print axioms coverage_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19
