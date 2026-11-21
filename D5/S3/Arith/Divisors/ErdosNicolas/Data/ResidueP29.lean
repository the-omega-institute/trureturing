/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP29
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP29.residue_step
   digest: Complete residue-tree certificate for largest prime 29. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP29

def initialVector (r : ℕ) : ℕ :=
  if r < 29 then
    if r < 14 then
      if r < 7 then
        if r < 3 then
          if r < 1 then
            0
          else
            if r < 2 then 122454469255 else 60247289093
        else
          if r < 5 then
            if r < 4 then 39580589023 else 29316694829
          else
            if r < 6 then 23229091534 else 19243457713
      else
        if r < 10 then
          if r < 8 then
            16472153014
          else
            if r < 9 then 14472906673 else 13001797428
        else
          if r < 12 then
            if r < 11 then 11914549438 else 11121800798
          else
            if r < 13 then 10566911869 else 10214247741
    else
      if r < 21 then
        if r < 17 then
          if r < 15 then
            10042799364
          else
            if r < 16 then 10042799364 else 10214247741
        else
          if r < 19 then
            if r < 18 then 10566911869 else 11121800798
          else
            if r < 20 then 11914549438 else 13001797428
      else
        if r < 25 then
          if r < 23 then
            if r < 22 then 14472906673 else 16472153014
          else
            if r < 24 then 19243457713 else 23229091534
        else
          if r < 27 then
            if r < 26 then 29316694829 else 39580589023
          else
            if r < 28 then 60247289093 else 122454469255
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 213859765499⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 216497761751⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 1], .prefix, 189074123161⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 184016419225⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 1], .prefix, 235284144799⟩,
    ⟨[0, 0, 0, 0, 0, 1, 1], .prefix, 160496085225⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 155897808530⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 196385950610⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 1], .prefix, 202473553905⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1], .prefix, 160496085225⟩,
    ⟨[0, 0, 0, 0, 1, 1], .prefix, 204037806887⟩,
    ⟨[0, 0, 0, 0, 1, 2], .prefix, 266847487444⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 156805361587⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 194243713331⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 1], .prefix, 201918664976⟩,
    ⟨[0, 0, 0, 1, 0, 0, 1], .prefix, 189074123161⟩,
    ⟨[0, 0, 0, 1, 0, 1], .prefix, 181245114526⟩,
    ⟨[0, 0, 0, 1, 0, 2], .prefix, 223717663773⟩,
    ⟨[0, 0, 0, 1, 1], .prefix, 213646818035⟩,
    ⟨[0, 0, 0, 1, 2], .prefix, 248297209027⟩,
    ⟨[0, 0, 0, 2], .prefix, 168243317098⟩,
    ⟨[0, 0, 0, 3], .prefix, 181245114526⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 1], .prefix, 213859765499⟩,
    ⟨[0, 0, 1, 0, 0, 0, 1], .prefix, 216497761751⟩,
    ⟨[0, 0, 1, 0, 0, 1], .prefix, 184016419225⟩,
    ⟨[0, 0, 1, 0, 0, 2], .prefix, 310597532926⟩,
    ⟨[0, 0, 1, 0, 1], .prefix, 196385950610⟩,
    ⟨[0, 0, 1, 0, 2], .prefix, 312976195228⟩,
    ⟨[0, 0, 1, 1], .prefix, 194243713331⟩,
    ⟨[0, 0, 1, 2], .prefix, 223717663773⟩,
    ⟨[0, 0, 1, 3], .prefix, 356386380769⟩,
    ⟨[0, 0, 2], .prefix, 175000255618⟩,
    ⟨[0, 0, 3], .prefix, 194243713331⟩,
    ⟨[0, 0, 4], .prefix, 210715866345⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 213859765499⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1, 1], .prefix, 406260082288⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 189074123161⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 235284144799⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 266442151950⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 202473553905⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 244804825186⟩,
    ⟨[0, 1, 0, 1], .prefix, 201918664976⟩,
    ⟨[0, 1, 0, 2], .prefix, 266229204486⟩,
    ⟨[0, 1, 0, 3], .prefix, 306112811184⟩,
    ⟨[0, 1, 1], .prefix, 213859765499⟩,
    ⟨[0, 1, 2], .prefix, 251561763706⟩,
    ⟨[0, 1, 3], .prefix, 308439642395⟩,
    ⟨[0, 1, 4], .prefix, 344582645784⟩,
    ⟨[0, 2], .prefix, 175036855706⟩,
    ⟨[0, 3], .prefix, 235284144799⟩,
    ⟨[0, 4], .prefix, 254527602512⟩,
    ⟨[0, 5], .prefix, 266442151950⟩,
    ⟨[0, 6], .prefix, 294966098139⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 29 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[0, 7], .prefix, 306880647577⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 217845399320⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 241525805084⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 216497761751⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 232496595112⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 267640236084⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 210295712160⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 245439353132⟩,
    ⟨[1, 0, 0, 1], .prefix, 226491359850⟩,
    ⟨[1, 0, 0, 2], .prefix, 276286196614⟩,
    ⟨[1, 0, 0, 3], .prefix, 306096566196⟩,
    ⟨[1, 0, 1], .prefix, 217845399320⟩,
    ⟨[1, 0, 2], .prefix, 261635000822⟩,
    ⟨[1, 0, 3], .prefix, 314681302680⟩,
    ⟨[1, 0, 4], .prefix, 342275256492⟩,
    ⟨[1, 1], .prefix, 241525805084⟩,
    ⟨[1, 2], .prefix, 266442151950⟩,
    ⟨[1, 3], .prefix, 389910210597⟩,
    ⟨[1, 4], .prefix, 448734257333⟩,
    ⟨[1, 5], .prefix, 483877898305⟩,
    ⟨[1, 6], .prefix, 562421839481⟩,
    ⟨[1, 7], .prefix, 597565480453⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 265057914293⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 1], .prefix, 281409411782⟩,
    ⟨[2, 0, 0, 0, 0, 0, 1], .prefix, 257729006018⟩,
    ⟨[2, 0, 0, 0, 0, 1], .prefix, 281056747654⟩,
    ⟨[2, 0, 0, 0, 0, 2], .prefix, 329202186054⟩,
    ⟨[2, 0, 0, 0, 1], .prefix, 276286196614⟩,
    ⟨[2, 0, 0, 0, 2], .prefix, 329325657730⟩,
    ⟨[2, 0, 0, 1], .prefix, 360987874810⟩,
    ⟨[2, 0, 0, 2], .prefix, 414991724053⟩,
    ⟨[2, 0, 0, 3], .prefix, 484030018530⟩,
    ⟨[2, 0, 1], .prefix, 265057914293⟩,
    ⟨[2, 0, 2], .prefix, 414027335926⟩,
    ⟨[2, 0, 3], .prefix, 483065630403⟩,
    ⟨[2, 0, 4], .prefix, 531211068803⟩,
    ⟨[2, 1], .prefix, 281409411782⟩,
    ⟨[2, 2], .prefix, 322005163022⟩,
    ⟨[2, 3], .prefix, 509839453030⟩,
    ⟨[2, 4], .prefix, 579230411635⟩,
    ⟨[2, 5], .prefix, 627375850035⟩,
    ⟨[2, 6], .prefix, 771222056500⟩,
    ⟨[2, 7], .prefix, 840613015105⟩,
    ⟨[3], .prefix, 226491359850⟩,
    ⟨[4], .prefix, 238533405555⟩,
    ⟨[5], .prefix, 276286196614⟩,
    ⟨[6], .prefix, 295529654327⟩,
    ⟨[7], .prefix, 306096566196⟩,
    ⟨[8], .prefix, 329325657730⟩,
    ⟨[9], .prefix, 341240207168⟩,
    ⟨[10], .prefix, 355840610108⟩,
    ⟨[11], .prefix, 367755159546⟩,
    ⟨[12], .prefix, 381835958408⟩,
    ⟨[13], .prefix, 391878757772⟩,
    ⟨[14], .prefix, 514333227027⟩,
    ⟨[15], .prefix, 574580516120⟩,
    ⟨[16], .prefix, 603897210949⟩,
    ⟨[17], .prefix, 618370117622⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 29 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 29 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 29 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 29) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 29 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 29,
      hHat (residueBoxValue 29 v / 29) ≤ ((residueBoxValue 29 v / 29).divisors.card : ℚ) →
      hHat (residueBoxValue 29 v) < ((residueBoxValue 29 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP29
