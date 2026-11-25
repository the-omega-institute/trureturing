/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP97
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP97.residue_step
   digest: Complete residue-tree certificate for largest prime 97. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP97

def initialVector (r : ℕ) : ℕ :=
  if r < 97 then
    if r < 48 then
      if r < 24 then
        if r < 12 then
          if r < 6 then
            if r < 3 then
              if r < 1 then
                0
              else
                if r < 2 then 418049447632 else 209751587492
            else
              if r < 4 then
                140326430011
              else
                if r < 5 then 105621025148 else 84804790034
          else
            if r < 9 then
              if r < 7 then
                70934205291
              else
                if r < 8 then 61033486489 else 53614750240
            else
              if r < 10 then
                47851404836
              else
                if r < 11 then 43247505379 else 39487460914
        else
          if r < 18 then
            if r < 15 then
              if r < 13 then
                36360889111
              else
                if r < 14 then 33722151066 else 31467230963
            else
              if r < 16 then
                29519862261
              else
                if r < 17 then 27822857640 else 26332498036
          else
            if r < 21 then
              if r < 19 then
                25014792321
              else
                if r < 20 then 23842919510 else 22795436007
            else
              if r < 22 then
                21854997242
              else
                if r < 23 then 21007426956 else 20241029374
      else
        if r < 36 then
          if r < 30 then
            if r < 27 then
              if r < 25 then
                19546073941
              else
                if r < 26 then 18914403539 else 18339133011
            else
              if r < 28 then
                17814414615
              else
                if r < 29 then 17335254500 else 16897367206
          else
            if r < 33 then
              if r < 31 then
                16497058585
              else
                if r < 32 then 16131132002 else 15796812772
            else
              if r < 34 then
                15491685401
              else
                if r < 35 then 15213643049 else 14960845044
        else
          if r < 42 then
            if r < 39 then
              if r < 37 then
                14731682447
              else
                if r < 38 then 14524748564 else 14338814890
            else
              if r < 40 then
                14172811224
              else
                if r < 41 then 14025808015 else 13897002394
          else
            if r < 45 then
              if r < 43 then
                13785707019
              else
                if r < 44 then 13691339114 else 13613413000
            else
              if r < 46 then
                13551533208
              else
                if r < 47 then 13505390017 else 13474753343
    else
      if r < 72 then
        if r < 60 then
          if r < 54 then
            if r < 51 then
              if r < 49 then
                13459472836
              else
                if r < 50 then 13459472836 else 13474753343
            else
              if r < 52 then
                13505390017
              else
                if r < 53 then 13551533208 else 13613413000
          else
            if r < 57 then
              if r < 55 then
                13691339114
              else
                if r < 56 then 13785707019 else 13897002394
            else
              if r < 58 then
                14025808015
              else
                if r < 59 then 14172811224 else 14338814890
        else
          if r < 66 then
            if r < 63 then
              if r < 61 then
                14524748564
              else
                if r < 62 then 14731682447 else 14960845044
            else
              if r < 64 then
                15213643049
              else
                if r < 65 then 15491685401 else 15796812772
          else
            if r < 69 then
              if r < 67 then
                16131132002
              else
                if r < 68 then 16497058585 else 16897367206
            else
              if r < 70 then
                17335254500
              else
                if r < 71 then 17814414615 else 18339133011
      else
        if r < 84 then
          if r < 78 then
            if r < 75 then
              if r < 73 then
                18914403539
              else
                if r < 74 then 19546073941 else 20241029374
            else
              if r < 76 then
                21007426956
              else
                if r < 77 then 21854997242 else 22795436007
          else
            if r < 81 then
              if r < 79 then
                23842919510
              else
                if r < 80 then 25014792321 else 26332498036
            else
              if r < 82 then
                27822857640
              else
                if r < 83 then 29519862261 else 31467230963
        else
          if r < 90 then
            if r < 87 then
              if r < 85 then
                33722151066
              else
                if r < 86 then 36360889111 else 39487460914
            else
              if r < 88 then
                43247505379
              else
                if r < 89 then 47851404836 else 53614750240
          else
            if r < 93 then
              if r < 91 then
                61033486489
              else
                if r < 92 then 70934205291 else 84804790034
            else
              if r < 95 then
                if r < 94 then 105621025148 else 140326430011
              else
                if r < 96 then 209751587492 else 418049447632
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      .prefix, 471664197872⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 479082934121⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 443064239953⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 523670472780⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 436388580643⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 434546506217⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 433010292676⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 438290477006⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 457536908546⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 433541133033⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 465900852468⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 436388580643⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 439904444874⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 436963851171⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 461296953011⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 438290477006⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 441892367142⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 444381945668⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 451771598698⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 481291460959⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 457536908546⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 537283885780⟩,
    ⟨[0, 0, 0, 1], .prefix, 479082934121⟩,
    ⟨[0, 0, 0, 2], .prefix, 659268266087⟩,
    ⟨[0, 0, 0, 3], .prefix, 720301752576⟩,
    ⟨[0, 0, 1], .prefix, 502854237666⟩,
    ⟨[0, 0, 2], .prefix, 521768641205⟩,
    ⟨[0, 0, 3], .prefix, 539103895705⟩,
    ⟨[0, 0, 4], .prefix, 553276706929⟩,
    ⟨[0, 1], .prefix, 558375877643⟩,
    ⟨[0, 2], .prefix, 606227282479⟩,
    ⟨[0, 3], .prefix, 624041697094⟩,
    ⟨[0, 4], .prefix, 651864554734⟩,
    ⟨[0, 5], .prefix, 753238184622⟩,
    ⟨[0, 6], .prefix, 893564614633⟩,
    ⟨[0, 7], .prefix, 941416019469⟩,
    ⟨[1], .prefix, 627801035124⟩,
    ⟨[2], .prefix, 733422060272⟩,
    ⟨[3], .prefix, 787036810512⟩,
    ⟨[4], .prefix, 814859668152⟩,
    ⟨[5], .prefix, 830656480924⟩,
    ⟨[6], .prefix, 908428106314⟩,
    ⟨[7], .prefix, 1014049131462⟩,
    ⟨[8], .prefix, 1067663881702⟩,
    ⟨[9], .prefix, 1095486739342⟩,
    ⟨[10], .prefix, 1111283552114⟩,
    ⟨[11], .prefix, 1127875896224⟩,
    ⟨[12], .prefix, 1143672708996⟩,
    ⟨[13], .prefix, 1187650918188⟩,
    ⟨[14], .prefix, 1215473775828⟩,
    ⟨[15], .prefix, 1231270588600⟩,
    ⟨[16], .prefix, 1261759219058⟩,
    ⟨[17], .prefix, 1289582076698⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 97 3 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0

private theorem all_checked :
    certificates.all (checkResidueTerminal 97 3 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 97 3 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 97) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 97 3 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 97,
      hHat (residueBoxValue 97 v / 97) ≤ ((residueBoxValue 97 v / 97).divisors.card : ℚ) →
      hHat (residueBoxValue 97 v) < ((residueBoxValue 97 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP97
