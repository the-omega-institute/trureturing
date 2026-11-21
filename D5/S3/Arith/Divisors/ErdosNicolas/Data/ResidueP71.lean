/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP71
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP71.residue_step
   digest: Complete residue-tree certificate for largest prime 71. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP71

def initialVector (r : ℕ) : ℕ :=
  if r < 71 then
    if r < 35 then
      if r < 17 then
        if r < 8 then
          if r < 4 then
            if r < 2 then
              if r < 1 then 0 else 296414100124
            else
              if r < 3 then 144005896233 else 93247108662
          else
            if r < 6 then
              if r < 5 then 67902150906 else 52723977445
            else
              if r < 7 then 42630303625 else 35443067203
        else
          if r < 12 then
            if r < 10 then
              if r < 9 then 30073292899 else 25916048288
            else
              if r < 11 then 22608426242 else 19919537814
          else
            if r < 14 then
              if r < 13 then 17695507970 else 15829859643
            else
              if r < 15 then
                14246589605
              else
                if r < 16 then 12890015041 else 11718427853
      else
        if r < 26 then
          if r < 21 then
            if r < 19 then
              if r < 18 then 10699989440 else 9809993506
            else
              if r < 20 then 9028995068 else 8341500293
          else
            if r < 23 then
              if r < 22 then 7735031641 else 7199448963
            else
              if r < 24 then
                6726447957
              else
                if r < 25 then 6309185146 else 5941993949
        else
          if r < 30 then
            if r < 28 then
              if r < 27 then 5620166640 else 5339786859
            else
              if r < 29 then 5097598333 else 4890902920
          else
            if r < 32 then
              if r < 31 then 4717480379 else 4575525748
            else
              if r < 33 then
                4463599857
              else
                if r < 34 then 4380592763 else 4325694498
    else
      if r < 53 then
        if r < 44 then
          if r < 39 then
            if r < 37 then
              if r < 36 then 4298376112 else 4298376112
            else
              if r < 38 then 4325694498 else 4380592763
          else
            if r < 41 then
              if r < 40 then 4463599857 else 4575525748
            else
              if r < 42 then
                4717480379
              else
                if r < 43 then 4890902920 else 5097598333
        else
          if r < 48 then
            if r < 46 then
              if r < 45 then 5339786859 else 5620166640
            else
              if r < 47 then 5941993949 else 6309185146
          else
            if r < 50 then
              if r < 49 then 6726447957 else 7199448963
            else
              if r < 51 then
                7735031641
              else
                if r < 52 then 8341500293 else 9028995068
      else
        if r < 62 then
          if r < 57 then
            if r < 55 then
              if r < 54 then 9809993506 else 10699989440
            else
              if r < 56 then 11718427853 else 12890015041
          else
            if r < 59 then
              if r < 58 then 14246589605 else 15829859643
            else
              if r < 60 then
                17695507970
              else
                if r < 61 then 19919537814 else 22608426242
        else
          if r < 66 then
            if r < 64 then
              if r < 63 then 25916048288 else 30073292899
            else
              if r < 65 then 35443067203 else 42630303625
          else
            if r < 68 then
              if r < 67 then 52723977445 else 67902150906
            else
              if r < 69 then
                93247108662
              else
                if r < 70 then 144005896233 else 296414100124
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 364316251030⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 331857167327⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 339044403749⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 364316251030⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 389661208786⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 301511698457⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 302034266764⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 303140548081⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 308132527977⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 303613549087⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 303140548081⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 309304115165⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 307114089564⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 316333637938⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 332163497581⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 316333637938⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 332163497581⟩,
    ⟨[0, 0, 0, 1], .prefix, 331857167327⟩,
    ⟨[0, 0, 0, 2], .prefix, 354465593569⟩,
    ⟨[0, 0, 0, 3], .prefix, 366543732911⟩,
    ⟨[0, 0, 1], .prefix, 349138077569⟩,
    ⟨[0, 0, 2], .prefix, 363384667174⟩,
    ⟨[0, 0, 3], .prefix, 374084656614⟩,
    ⟨[0, 0, 4], .prefix, 380026650563⟩,
    ⟨[0, 1], .prefix, 389661208786⟩,
    ⟨[0, 2], .prefix, 415577257074⟩,
    ⟨[0, 3], .prefix, 426043686831⟩,
    ⟨[0, 4], .prefix, 451959735119⟩,
    ⟨[0, 5], .prefix, 469221785675⟩,
    ⟨[0, 6], .prefix, 495137833963⟩,
    ⟨[0, 7], .prefix, 500758000603⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 538395440162⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 490109653165⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 500745807952⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 538395440162⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 576297408644⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 497524566565⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 465057014550⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 537992799517⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 470911570393⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 461140758920⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 537992799517⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 458027491777⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 455445680295⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 467538983134⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 488989009417⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 467538983134⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 488989009417⟩,
    ⟨[1, 0, 0, 1], .prefix, 490109653165⟩,
    ⟨[1, 0, 0, 2], .prefix, 521059579700⟩,
    ⟨[1, 0, 0, 3], .prefix, 552416497050⟩,
    ⟨[1, 0, 1], .prefix, 515752400044⟩,
    ⟨[1, 0, 2], .prefix, 535096587982⟩,
    ⟨[1, 0, 3], .prefix, 550122271920⟩,
    ⟨[1, 0, 4], .prefix, 563799297510⟩,
    ⟨[1, 1], .prefix, 576297408644⟩,
    ⟨[1, 2], .prefix, 612023450438⟩,
    ⟨[1, 3], .prefix, 631124762499⟩,
    ⟨[1, 4], .prefix, 666850804293⟩,
    ⟨[1, 5], .prefix, 693440353868⟩,
    ⟨[1, 6], .prefix, 729166395662⟩,
    ⟨[1, 7], .prefix, 745206171961⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 71 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[2], .prefix, 508322147263⟩,
    ⟨[3], .prefix, 538395440162⟩,
    ⟨[4], .prefix, 550113868015⟩,
    ⟨[5], .prefix, 554577467872⟩,
    ⟨[6], .prefix, 590020535075⟩,
    ⟨[7], .prefix, 604267124680⟩,
    ⟨[8], .prefix, 609364723013⟩,
    ⟨[9], .prefix, 636595994897⟩,
    ⟨[10], .prefix, 666669287796⟩,
    ⟨[11], .prefix, 678387715649⟩,
    ⟨[12], .prefix, 682851315506⟩,
    ⟨[13], .prefix, 718294382709⟩,
    ⟨[14], .prefix, 732540972314⟩,
    ⟨[15], .prefix, 737638570647⟩,
    ⟨[16], .prefix, 767703784669⟩,
    ⟨[17], .prefix, 810334088294⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 71 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 71 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 71 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 71) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 71 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 71,
      hHat (residueBoxValue 71 v / 71) ≤ ((residueBoxValue 71 v / 71).divisors.card : ℚ) →
      hHat (residueBoxValue 71 v) < ((residueBoxValue 71 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP71
