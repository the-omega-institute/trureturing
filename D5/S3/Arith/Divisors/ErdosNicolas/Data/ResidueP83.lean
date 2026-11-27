/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP83
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP83.residue_step
   digest: Complete residue-tree certificate for largest prime 83. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP83

def initialVector (r : ℕ) : ℕ :=
  if r < 83 then
    if r < 41 then
      if r < 20 then
        if r < 10 then
          if r < 5 then
            if r < 2 then
              if r < 1 then 0 else 347944728630
            else
              if r < 3 then
                169757256800
              else
                if r < 4 then 110398555326 else 80748103529
          else
            if r < 7 then
              if r < 6 then 62981841064 else 51158452552
            else
              if r < 8 then
                42731695367
              else
                if r < 9 then 36428480981 else 31541569216
        else
          if r < 15 then
            if r < 12 then
              if r < 11 then 27646645729 else 24473721563
            else
              if r < 13 then
                21842832632
              else
                if r < 14 then 19629416520 else 17744528518
          else
            if r < 17 then
              if r < 16 then 16122970466 else 14715872130
            else
              if r < 18 then
                13485891229
              else
                if r < 19 then 12404012457 else 11447359437
      else
        if r < 30 then
          if r < 25 then
            if r < 22 then
              if r < 21 then 10597661462 else 9840159472
            else
              if r < 23 then
                9162810333
              else
                if r < 24 then 8555699446 else 8010599353
          else
            if r < 27 then
              if r < 26 then 7520635911 else 7080030494
            else
              if r < 28 then
                6683900876
              else
                if r < 29 then 6328104527 else 6009114611
        else
          if r < 35 then
            if r < 32 then
              if r < 31 then 5723921880 else 5469955326
            else
              if r < 33 then
                5245018354
              else
                if r < 34 then 5047237405 else 4875019958
          else
            if r < 38 then
              if r < 36 then
                4727020666
              else
                if r < 37 then 4602113385 else 4499369511
            else
              if r < 39 then
                4418039554
              else
                if r < 40 then 4357539775 else 4317441064
    else
      if r < 62 then
        if r < 51 then
          if r < 46 then
            if r < 43 then
              if r < 42 then 4297461553 else 4297461553
            else
              if r < 44 then
                4317441064
              else
                if r < 45 then 4357539775 else 4418039554
          else
            if r < 48 then
              if r < 47 then 4499369511 else 4602113385
            else
              if r < 49 then
                4727020666
              else
                if r < 50 then 4875019958 else 5047237405
        else
          if r < 56 then
            if r < 53 then
              if r < 52 then 5245018354 else 5469955326
            else
              if r < 54 then
                5723921880
              else
                if r < 55 then 6009114611 else 6328104527
          else
            if r < 59 then
              if r < 57 then
                6683900876
              else
                if r < 58 then 7080030494 else 7520635911
            else
              if r < 60 then
                8010599353
              else
                if r < 61 then 8555699446 else 9162810333
      else
        if r < 72 then
          if r < 67 then
            if r < 64 then
              if r < 63 then 9840159472 else 10597661462
            else
              if r < 65 then
                11447359437
              else
                if r < 66 then 12404012457 else 13485891229
          else
            if r < 69 then
              if r < 68 then 14715872130 else 16122970466
            else
              if r < 70 then
                17744528518
              else
                if r < 71 then 19629416520 else 21842832632
        else
          if r < 77 then
            if r < 74 then
              if r < 73 then 24473721563 else 27646645729
            else
              if r < 75 then
                31541569216
              else
                if r < 76 then 36428480981 else 42731695367
          else
            if r < 80 then
              if r < 78 then
                51158452552
              else
                if r < 79 then 62981841064 else 80748103529
            else
              if r < 81 then
                110398555326
              else
                if r < 82 then 169757256800 else 347944728630
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 428692832159⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 375591374359⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 390676423997⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 362660600760⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 357107538963⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 355955327983⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 353668650510⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 353668650510⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 354628629506⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], .kernel, 352242190183⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 634878569940⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 555946292621⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 578178209315⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 537662875914⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 538699975854⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 564851720351⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 546777820378⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 546777820378⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 632417981820⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 379486297846⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 384373209611⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 358542390092⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 360348741087⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 359392088067⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 361430619859⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 367574145150⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 477972700476⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 372418450193⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 388541420659⟩,
    ⟨[0, 0, 0, 1], .prefix, 390676423997⟩,
    ⟨[0, 0, 0, 2], .prefix, 412519256629⟩,
    ⟨[0, 0, 0, 3], .prefix, 421682066962⟩,
    ⟨[0, 0, 1], .prefix, 410926569694⟩,
    ⟨[0, 0, 2], .prefix, 418447205605⟩,
    ⟨[0, 0, 3], .prefix, 550395868564⟩,
    ⟨[0, 0, 4], .prefix, 613377709628⟩,
    ⟨[0, 1], .prefix, 458343283956⟩,
    ⟨[0, 2], .prefix, 489884853172⟩,
    ⟨[0, 3], .prefix, 496568754048⟩,
    ⟨[0, 4], .prefix, 666326010848⟩,
    ⟨[0, 5], .prefix, 717484463400⟩,
    ⟨[0, 6], .prefix, 729888475857⟩,
    ⟨[0, 7], .prefix, 736216580384⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 634878569940⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 555946292621⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 578178209315⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 537662875914⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 538699975854⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 564851720351⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 546777820378⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 546777820378⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 632417981820⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 869944175613⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 561647567103⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 568846338541⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 532617087956⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 534708111272⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 542058422616⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 585041366269⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 544411432444⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 705968440322⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 551338517326⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 83 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 0, 2], .prefix, 598488252247⟩,
    ⟨[1, 0, 0, 1], .prefix, 578178209315⟩,
    ⟨[1, 0, 0, 2], .prefix, 608031641300⟩,
    ⟨[1, 0, 0, 3], .prefix, 632812731635⟩,
    ⟨[1, 0, 1], .prefix, 608330472223⟩,
    ⟨[1, 0, 2], .prefix, 626863600857⟩,
    ⟨[1, 0, 3], .prefix, 973140535722⟩,
    ⟨[1, 0, 4], .prefix, 1040479916561⟩,
    ⟨[1, 1], .prefix, 679258993308⟩,
    ⟨[1, 2], .prefix, 723204574981⟩,
    ⟨[1, 3], .prefix, 736216580384⟩,
    ⟨[1, 4], .prefix, 1033713116133⟩,
    ⟨[1, 5], .prefix, 1195270124011⟩,
    ⟨[1, 6], .prefix, 1239215705684⟩,
    ⟨[1, 7], .prefix, 1263288338729⟩,
    ⟨[2], .prefix, 598450088959⟩,
    ⟨[3], .prefix, 634878569940⟩,
    ⟨[4], .prefix, 649594442070⟩,
    ⟨[5], .prefix, 654839460424⟩,
    ⟨[6], .prefix, 666286819861⟩,
    ⟨[7], .prefix, 670704859415⟩,
    ⟨[8], .prefix, 713436554782⟩,
    ⟨[9], .prefix, 731181083300⟩,
    ⟨[10], .prefix, 737509187827⟩,
    ⟨[11], .prefix, 760156469324⟩,
    ⟨[12], .prefix, 840904572853⟩,
    ⟨[13], .prefix, 877333053834⟩,
    ⟨[14], .prefix, 892048925964⟩,
    ⟨[15], .prefix, 897293944318⟩,
    ⟨[16], .prefix, 946448162172⟩,
    ⟨[17], .prefix, 982876643153⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 83 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 83 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 83 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 83) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 83 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 83,
      hHat (residueBoxValue 83 v / 83) ≤ ((residueBoxValue 83 v / 83).divisors.card : ℚ) →
      hHat (residueBoxValue 83 v) < ((residueBoxValue 83 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP83
