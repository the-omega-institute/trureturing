/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP59
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP59.residue_step
   digest: Complete residue-tree certificate for largest prime 59. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP59

def initialVector (r : ℕ) : ℕ :=
  if r < 59 then
    if r < 29 then
      if r < 14 then
        if r < 7 then
          if r < 3 then
            if r < 1 then
              0
            else
              if r < 2 then 251276409883 else 124600959259
          else
            if r < 5 then
              if r < 4 then 82398494492 else 61318299296
            else
              if r < 6 then 48690289815 else 40291169467
        else
          if r < 10 then
            if r < 8 then
              34311023867
            else
              if r < 9 then 29844969366 else 26390370863
          else
            if r < 12 then
              if r < 11 then 23645729449 else 21419268515
            else
              if r < 13 then 19583227809 else 18049254182
      else
        if r < 21 then
          if r < 17 then
            if r < 15 then
              16754339823
            else
              if r < 16 then 15652386793 else 14708936201
          else
            if r < 19 then
              if r < 18 then 13897759892 else 13198588947
            else
              if r < 20 then 12595563045 else 12076145748
        else
          if r < 25 then
            if r < 23 then
              if r < 22 then 11630354197 else 11250199556
            else
              if r < 24 then 10929279322 else 10662473593
          else
            if r < 27 then
              if r < 26 then 10445719983 else 10275844941
            else
              if r < 28 then 10150439497 else 10067769169
    else
      if r < 44 then
        if r < 36 then
          if r < 32 then
            if r < 30 then
              10026710007
            else
              if r < 31 then 10026710007 else 10067769169
          else
            if r < 34 then
              if r < 33 then 10150439497 else 10275844941
            else
              if r < 35 then 10445719983 else 10662473593
        else
          if r < 40 then
            if r < 38 then
              if r < 37 then 10929279322 else 11250199556
            else
              if r < 39 then 11630354197 else 12076145748
          else
            if r < 42 then
              if r < 41 then 12595563045 else 13198588947
            else
              if r < 43 then 13897759892 else 14708936201
      else
        if r < 51 then
          if r < 47 then
            if r < 45 then
              15652386793
            else
              if r < 46 then 16754339823 else 18049254182
          else
            if r < 49 then
              if r < 48 then 19583227809 else 21419268515
            else
              if r < 50 then 23645729449 else 26390370863
        else
          if r < 55 then
            if r < 53 then
              if r < 52 then 29844969366 else 34311023867
            else
              if r < 54 then 40291169467 else 48690289815
          else
            if r < 57 then
              if r < 56 then 61318299296 else 82398494492
            else
              if r < 58 then 124600959259 else 251276409883
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 291567579350⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 299966699698⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 272695678398⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 264474998830⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 281121379249⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 263871972928⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], .kernel, 261303119890⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 435751766418⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 448213388406⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 408546837213⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 404855902646⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 420431274709⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 468343632803⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 264474998830⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 263871972928⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 285587433750⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 277666780746⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 299170633431⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 272695678398⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 355094172890⟩,
    ⟨[0, 0, 0, 1], .prefix, 285587433750⟩,
    ⟨[0, 0, 0, 2], .prefix, 309233163199⟩,
    ⟨[0, 0, 0, 3], .prefix, 339776363109⟩,
    ⟨[0, 0, 1], .prefix, 299966699698⟩,
    ⟨[0, 0, 2], .prefix, 319549927507⟩,
    ⟨[0, 0, 3], .prefix, 344723443548⟩,
    ⟨[0, 0, 4], .prefix, 364306671357⟩,
    ⟨[0, 1], .prefix, 333674904375⟩,
    ⟨[0, 2], .prefix, 360065275238⟩,
    ⟨[0, 3], .prefix, 372141420986⟩,
    ⟨[0, 4], .prefix, 390190675168⟩,
    ⟨[0, 5], .prefix, 415776938158⟩,
    ⟨[0, 6], .prefix, 430698118127⟩,
    ⟨[0, 7], .prefix, 488725591651⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 435751766418⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 448213388406⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 408546837213⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 404855902646⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 420431274709⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 468343632803⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 637180489032⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 404855902646⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 468343632803⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 426942732832⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 415466328952⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 448756373832⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 408546837213⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 531236501172⟩,
    ⟨[1, 0, 0, 1], .prefix, 426942732832⟩,
    ⟨[1, 0, 0, 2], .prefix, 462664608029⟩,
    ⟨[1, 0, 0, 3], .prefix, 511160609983⟩,
    ⟨[1, 0, 1], .prefix, 448213388406⟩,
    ⟨[1, 0, 2], .prefix, 485049479252⟩,
    ⟨[1, 0, 3], .prefix, 536114842942⟩,
    ⟨[1, 0, 4], .prefix, 568196585050⟩,
    ⟨[1, 1], .prefix, 498567033101⟩,
    ⟨[1, 2], .prefix, 538155992911⟩,
    ⟨[1, 3], .prefix, 596996722223⟩,
    ⟨[1, 4], .prefix, 623899308572⟩,
    ⟨[1, 5], .prefix, 674964672262⟩,
    ⟨[1, 6], .prefix, 700492786351⟩,
    ⟨[1, 7], .prefix, 791656055013⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 59 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[2], .prefix, 437195668438⟩,
    ⟨[3], .prefix, 467040637804⟩,
    ⟨[4], .prefix, 481749574005⟩,
    ⟨[5], .prefix, 492719734604⟩,
    ⟨[6], .prefix, 540590303317⟩,
    ⟨[7], .prefix, 564236032766⟩,
    ⟨[8], .prefix, 576312178514⟩,
    ⟨[9], .prefix, 589915129566⟩,
    ⟨[10], .prefix, 648479598670⟩,
    ⟨[11], .prefix, 678324568036⟩,
    ⟨[12], .prefix, 693033504237⟩,
    ⟨[13], .prefix, 709612731529⟩,
    ⟨[14], .prefix, 751874233549⟩,
    ⟨[15], .prefix, 775519962998⟩,
    ⟨[16], .prefix, 787596108746⟩,
    ⟨[17], .prefix, 813007366408⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 59 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 59 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 59 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 59) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 59 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 59,
      hHat (residueBoxValue 59 v / 59) ≤ ((residueBoxValue 59 v / 59).divisors.card : ℚ) →
      hHat (residueBoxValue 59 v) < ((residueBoxValue 59 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP59
