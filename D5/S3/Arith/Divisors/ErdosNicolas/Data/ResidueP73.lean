/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP73
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP73.residue_step
   digest: Complete residue-tree certificate for largest prime 73. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP73

def initialVector (r : ℕ) : ℕ :=
  if r < 73 then
    if r < 36 then
      if r < 18 then
        if r < 9 then
          if r < 4 then
            if r < 2 then
              if r < 1 then 0 else 305002330372
            else
              if r < 3 then 148297356770 else 96105006378
          else
            if r < 6 then
              if r < 5 then 70042202183 else 54432394424
            else
              if r < 7 then
                44050124841
              else
                if r < 8 then 36655965572 else 31130253348
        else
          if r < 13 then
            if r < 11 then
              if r < 10 then 26851002181 else 23445067607
            else
              if r < 12 then 20675040632 else 18382694778
          else
            if r < 15 then
              if r < 14 then 16458535009 else 14824396867
            else
              if r < 16 then
                13423007107
              else
                if r < 17 then 12211458592 else 11156989725
      else
        if r < 27 then
          if r < 22 then
            if r < 20 then
              if r < 19 then 10234169642 else 9422974151
            else
              if r < 21 then 8707438444 else 8074695906
          else
            if r < 24 then
              if r < 23 then 7514278921 else 7017603127
            else
              if r < 25 then
                6577581757
              else
                if r < 26 then 6188332106 else 5844951421
        else
          if r < 31 then
            if r < 29 then
              if r < 28 then 5543343526 else 5280082896
            else
              if r < 30 then 5052308807 else 4857641386
          else
            if r < 33 then
              if r < 32 then 4694115692 else 4560129156
            else
              if r < 34 then
                4454401796
              else
                if r < 35 then 4375943367 else 4324031096
    else
      if r < 54 then
        if r < 45 then
          if r < 40 then
            if r < 38 then
              if r < 37 then 4298191870 else 4298191870
            else
              if r < 39 then 4324031096 else 4375943367
          else
            if r < 42 then
              if r < 41 then 4454401796 else 4560129156
            else
              if r < 43 then
                4694115692
              else
                if r < 44 then 4857641386 else 5052308807
        else
          if r < 49 then
            if r < 47 then
              if r < 46 then 5280082896 else 5543343526
            else
              if r < 48 then 5844951421 else 6188332106
          else
            if r < 51 then
              if r < 50 then 6577581757 else 7017603127
            else
              if r < 52 then
                7514278921
              else
                if r < 53 then 8074695906 else 8707438444
      else
        if r < 63 then
          if r < 58 then
            if r < 56 then
              if r < 55 then 9422974151 else 10234169642
            else
              if r < 57 then 11156989725 else 12211458592
          else
            if r < 60 then
              if r < 59 then 13423007107 else 14824396867
            else
              if r < 61 then
                16458535009
              else
                if r < 62 then 18382694778 else 20675040632
        else
          if r < 68 then
            if r < 65 then
              if r < 64 then 23445067607 else 26851002181
            else
              if r < 66 then
                31130253348
              else
                if r < 67 then 36655965572 else 44050124841
          else
            if r < 70 then
              if r < 69 then 54432394424 else 70042202183
            else
              if r < 71 then
                96105006378
              else
                if r < 72 then 148297356770 else 305002330372
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 349052455213⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 349052455213⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 319826727239⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 325677371004⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 319826727239⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 316159320097⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 317213788964⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], .kernel, 309300522242⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 762600209384⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 515732506761⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 515732506761⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 473404166905⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 481489006695⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 473404166905⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 474615863537⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 484710818479⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 309696446064⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 359434724796⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 314425304523⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 314425304523⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 316159320097⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 321460865381⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 328478468508⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 325677371004⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 334384809448⟩,
    ⟨[0, 0, 0, 1], .prefix, 341658295944⟩,
    ⟨[0, 0, 0, 2], .prefix, 409182032656⟩,
    ⟨[0, 0, 0, 3], .prefix, 445837998228⟩,
    ⟨[0, 0, 1], .prefix, 359434724796⟩,
    ⟨[0, 0, 2], .prefix, 365623056902⟩,
    ⟨[0, 0, 3], .prefix, 373697752808⟩,
    ⟨[0, 0, 4], .prefix, 405467030271⟩,
    ⟨[0, 1], .prefix, 401107336750⟩,
    ⟨[0, 2], .prefix, 427958338931⟩,
    ⟨[0, 3], .prefix, 438815171855⟩,
    ⟨[0, 4], .prefix, 465666174036⟩,
    ⟨[0, 5], .prefix, 471209517562⟩,
    ⟨[0, 6], .prefix, 776211847934⟩,
    ⟨[0, 7], .prefix, 872316854312⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 762600209384⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 515732506761⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 515732506761⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 473404166905⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 481489006695⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 473404166905⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 474615863537⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 484710818479⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 762600209384⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 494410054510⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 531177149173⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 467046692389⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 467046692389⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 474615863537⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 475603173572⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 492040246193⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 481489006695⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 566890564856⟩,
    ⟨[1, 0, 0, 1], .prefix, 504780049581⟩,
    ⟨[1, 0, 0, 2], .prefix, 606223629959⟩,
    ⟨[1, 0, 0, 3], .prefix, 657703992398⟩,
    ⟨[1, 0, 1], .prefix, 531177149173⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 73 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 2], .prefix, 572204040530⟩,
    ⟨[1, 0, 3], .prefix, 650081502561⟩,
    ⟨[1, 0, 4], .prefix, 701561865000⟩,
    ⟨[1, 1], .prefix, 593454818361⟩,
    ⟨[1, 2], .prefix, 630539990184⟩,
    ⟨[1, 3], .prefix, 649562444164⟩,
    ⟨[1, 4], .prefix, 688848019801⟩,
    ⟨[1, 5], .prefix, 701613933664⟩,
    ⟨[1, 6], .prefix, 1154913620806⟩,
    ⟨[1, 7], .prefix, 1295068752025⟩,
    ⟨[2], .prefix, 523341889325⟩,
    ⟨[3], .prefix, 554472142673⟩,
    ⟨[4], .prefix, 566683601265⟩,
    ⟨[5], .prefix, 571243730421⟩,
    ⟨[6], .prefix, 598094732602⟩,
    ⟨[7], .prefix, 608328902244⟩,
    ⟨[8], .prefix, 612627094114⟩,
    ⟨[9], .prefix, 917629424486⟩,
    ⟨[10], .prefix, 1065926781256⟩,
    ⟨[11], .prefix, 1135968983439⟩,
    ⟨[12], .prefix, 1167099236787⟩,
    ⟨[13], .prefix, 1179310695379⟩,
    ⟨[14], .prefix, 1183870824535⟩,
    ⟨[15], .prefix, 1210721826716⟩,
    ⟨[16], .prefix, 1220955996358⟩,
    ⟨[17], .prefix, 1225254188228⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 73 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 73 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 73 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 73) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 73 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 73,
      hHat (residueBoxValue 73 v / 73) ≤ ((residueBoxValue 73 v / 73).divisors.card : ℚ) →
      hHat (residueBoxValue 73 v) < ((residueBoxValue 73 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP73
