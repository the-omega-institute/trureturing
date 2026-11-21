/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP89
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP89.residue_step
   digest: Complete residue-tree certificate for largest prime 89. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP89

def initialVector (r : ℕ) : ℕ :=
  if r < 89 then
    if r < 44 then
      if r < 22 then
        if r < 11 then
          if r < 5 then
            if r < 2 then
              if r < 1 then 0 else 373710961239
            else
              if r < 3 then
                182634845033
              else
                if r < 4 then 118977253095 else 87175203940
          else
            if r < 8 then
              if r < 6 then
                68116136248
              else
                if r < 7 then 55429226565 else 46384150335
            else
              if r < 9 then
                39615770912
              else
                if r < 10 then 34365703721 else 30178941157
        else
          if r < 16 then
            if r < 13 then
              if r < 12 then 26765955985 else 23933751883
            else
              if r < 14 then
                21548737804
              else
                if r < 15 then 19515513402 else 17764139629
          else
            if r < 19 then
              if r < 17 then
                16242183737
              else
                if r < 18 then 14909572052 else 13735157689
            else
              if r < 20 then
                12694373355
              else
                if r < 21 then 11767587964 else 10938932905
      else
        if r < 33 then
          if r < 27 then
            if r < 24 then
              if r < 23 then 10195448265 else 9526452620
            else
              if r < 25 then
                8923069911
              else
                if r < 26 then 8377870596 else 7884595127
          else
            if r < 30 then
              if r < 28 then
                7437939282
              else
                if r < 29 then 7033386222 else 6667072902
            else
              if r < 31 then
                6335683449
              else
                if r < 32 then 6036364078 else 5766652960
        else
          if r < 38 then
            if r < 35 then
              if r < 34 then 5524425042 else 5307844699
            else
              if r < 36 then
                5115328888
              else
                if r < 37 then 4945515375 else 4797237459
          else
            if r < 41 then
              if r < 39 then
                4669502790
              else
                if r < 40 then 4561475569 else 4472463465
            else
              if r < 42 then
                4401905066
              else
                if r < 43 then 4349361602 else 4314509736
    else
      if r < 66 then
        if r < 55 then
          if r < 49 then
            if r < 46 then
              if r < 45 then 4297136580 else 4297136580
            else
              if r < 47 then
                4314509736
              else
                if r < 48 then 4349361602 else 4401905066
          else
            if r < 52 then
              if r < 50 then
                4472463465
              else
                if r < 51 then 4561475569 else 4669502790
            else
              if r < 53 then
                4797237459
              else
                if r < 54 then 4945515375 else 5115328888
        else
          if r < 60 then
            if r < 57 then
              if r < 56 then 5307844699 else 5524425042
            else
              if r < 58 then
                5766652960
              else
                if r < 59 then 6036364078 else 6335683449
          else
            if r < 63 then
              if r < 61 then
                6667072902
              else
                if r < 62 then 7033386222 else 7437939282
            else
              if r < 64 then
                7884595127
              else
                if r < 65 then 8377870596 else 8923069911
      else
        if r < 77 then
          if r < 71 then
            if r < 68 then
              if r < 67 then 9526452620 else 10195448265
            else
              if r < 69 then
                10938932905
              else
                if r < 70 then 11767587964 else 12694373355
          else
            if r < 74 then
              if r < 72 then
                13735157689
              else
                if r < 73 then 14909572052 else 16242183737
            else
              if r < 75 then
                17764139629
              else
                if r < 76 then 19515513402 else 21548737804
        else
          if r < 83 then
            if r < 80 then
              if r < 78 then
                23933751883
              else
                if r < 79 then 26765955985 else 30178941157
            else
              if r < 81 then
                34365703721
              else
                if r < 82 then 39615770912 else 46384150335
          else
            if r < 86 then
              if r < 84 then
                55429226565
              else
                if r < 85 then 68116136248 else 87175203940
            else
              if r < 87 then
                118977253095
              else
                if r < 88 then 182634845033 else 373710961239
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 429140187804⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 408076664960⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 389953144976⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 441827097487⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 460886165179⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 380744347461⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 492688214334⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 378656476614⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 378656476614⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 380378034141⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 395259699043⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 397644713122⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 383237413859⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 380378034141⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 383237413859⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 393226474641⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 388620533291⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 395259699043⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 429625402764⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 413326732151⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 440092688136⟩,
    ⟨[0, 0, 0, 1], .prefix, 420095111574⟩,
    ⟨[0, 0, 0, 2], .prefix, 424764614364⟩,
    ⟨[0, 0, 0, 3], .prefix, 446116312843⟩,
    ⟨[0, 0, 1], .prefix, 441827097487⟩,
    ⟨[0, 0, 2], .prefix, 455562255176⟩,
    ⟨[0, 0, 3], .prefix, 463940125772⟩,
    ⟨[0, 0, 4], .prefix, 637785328491⟩,
    ⟨[0, 1], .prefix, 492688214334⟩,
    ⟨[0, 2], .prefix, 527053918055⟩,
    ⟨[0, 3], .prefix, 534491857337⟩,
    ⟨[0, 4], .prefix, 574107628249⟩,
    ⟨[0, 5], .prefix, 583030698160⟩,
    ⟨[0, 6], .prefix, 610622252855⟩,
    ⟨[0, 7], .prefix, 619545322766⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 635708784720⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 604446667682⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 587673237826⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 654640883677⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 683136781124⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 574155508515⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 730752285932⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 628811304122⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 628811304122⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 679637569103⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 607131861673⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 589202628066⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 570186768628⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 679637569103⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 570186768628⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 582894705896⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 576563223023⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 607131861673⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 649078390794⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 612203760921⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 649165165171⟩,
    ⟨[1, 0, 0, 1], .prefix, 622245470009⟩,
    ⟨[1, 0, 0, 2], .prefix, 661083637195⟩,
    ⟨[1, 0, 0, 3], .prefix, 690516970126⟩,
    ⟨[1, 0, 1], .prefix, 654640883677⟩,
    ⟨[1, 0, 2], .prefix, 673321556741⟩,
    ⟨[1, 0, 3], .prefix, 687466080297⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 89 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 4], .prefix, 1039644598561⟩,
    ⟨[1, 1], .prefix, 730752285932⟩,
    ⟨[1, 2], .prefix, 778853147342⟩,
    ⟨[1, 3], .prefix, 791855903693⟩,
    ⟨[1, 4], .prefix, 847264370161⟩,
    ⟨[1, 5], .prefix, 860589345138⟩,
    ⟨[1, 6], .prefix, 902213655633⟩,
    ⟨[1, 7], .prefix, 917264533295⟩,
    ⟨[2], .prefix, 643521010212⟩,
    ⟨[3], .prefix, 683136781124⟩,
    ⟨[4], .prefix, 699378964861⟩,
    ⟨[5], .prefix, 705145617821⟩,
    ⟨[6], .prefix, 724395321954⟩,
    ⟨[7], .prefix, 740637505691⟩,
    ⟨[8], .prefix, 746404158651⟩,
    ⟨[9], .prefix, 755046368236⟩,
    ⟨[10], .prefix, 759343504816⟩,
    ⟨[11], .prefix, 1133054466055⟩,
    ⟨[12], .prefix, 1315689311088⟩,
    ⟨[13], .prefix, 1402864515028⟩,
    ⟨[14], .prefix, 1442480285940⟩,
    ⟨[15], .prefix, 1458722469677⟩,
    ⟨[16], .prefix, 1464489122637⟩,
    ⟨[17], .prefix, 1483738826770⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 89 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 89 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 89 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 89) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 89 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 89,
      hHat (residueBoxValue 89 v / 89) ≤ ((residueBoxValue 89 v / 89).divisors.card : ℚ) →
      hHat (residueBoxValue 89 v) < ((residueBoxValue 89 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP89
