/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP43
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP43.residue_step
   digest: Complete residue-tree certificate for largest prime 43. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP43

def initialVector (r : ℕ) : ℕ :=
  if r < 43 then
    if r < 21 then
      if r < 10 then
        if r < 5 then
          if r < 2 then
            if r < 1 then 0 else 182566022947
          else
            if r < 3 then
              90264067002
            else
              if r < 4 then 59533350226 else 44203150444
        else
          if r < 7 then
            if r < 6 then 35039530782 else 28964743493
          else
            if r < 8 then
              24660007430
            else
              if r < 9 then 21466206854 else 19017463709
      else
        if r < 15 then
          if r < 12 then
            if r < 11 then 17094573498 else 15558392564
          else
            if r < 13 then
              14316540739
            else
              if r < 14 then 13305481825 else 12480296216
        else
          if r < 18 then
            if r < 16 then
              11808557741
            else
              if r < 17 then 11266523305 else 10836687866
          else
            if r < 19 then
              10506176665
            else
              if r < 20 then 10265676289 else 10108721258
    else
      if r < 32 then
        if r < 26 then
          if r < 23 then
            if r < 22 then 10031231044 else 10031231044
          else
            if r < 24 then
              10108721258
            else
              if r < 25 then 10265676289 else 10506176665
        else
          if r < 29 then
            if r < 27 then
              10836687866
            else
              if r < 28 then 11266523305 else 11808557741
          else
            if r < 30 then
              12480296216
            else
              if r < 31 then 13305481825 else 14316540739
      else
        if r < 37 then
          if r < 34 then
            if r < 33 then 15558392564 else 17094573498
          else
            if r < 35 then
              19017463709
            else
              if r < 36 then 21466206854 else 24660007430
        else
          if r < 40 then
            if r < 38 then
              28964743493
            else
              if r < 39 then 35039530782 else 44203150444
          else
            if r < 41 then
              59533350226
            else
              if r < 42 then 90264067002 else 182566022947
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 211530766440⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 196882563686⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], .kernel, 195046319163⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 361328183668⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 314275129658⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 281075921342⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 194374580688⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 201583486656⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 217605553729⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 199660596445⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 255404854998⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], .kernel, 198124415511⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 338499447247⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 265999593173⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 276125244912⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 300619064356⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 265842638142⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 1], .prefix, 270446644530⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1], .prefix, 271917425431⟩,
    ⟨[0, 0, 0, 0, 1, 1], .prefix, 303397097115⟩,
    ⟨[0, 0, 0, 0, 1, 2], .prefix, 335720042649⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 242327565955⟩,
    ⟨[0, 0, 0, 1], .prefix, 211530766440⟩,
    ⟨[0, 0, 0, 2], .prefix, 236190773870⟩,
    ⟨[0, 0, 0, 3], .prefix, 418756796817⟩,
    ⟨[0, 0, 1], .prefix, 217605553729⟩,
    ⟨[0, 0, 2], .prefix, 228442241595⟩,
    ⟨[0, 0, 3], .prefix, 272314880838⟩,
    ⟨[0, 0, 4], .prefix, 283151568704⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 361328183668⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 314275129658⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 281075921342⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 437145692336⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 344171997916⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 273597133098⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 288947461696⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 299608005442⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 467545747659⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 300619064356⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 346925118443⟩,
    ⟨[0, 1, 0, 1], .prefix, 314275129658⟩,
    ⟨[0, 1, 0, 2], .prefix, 353251677827⟩,
    ⟨[0, 1, 0, 3], .prefix, 558360904978⟩,
    ⟨[0, 1, 1], .prefix, 288947461696⟩,
    ⟨[0, 1, 2], .prefix, 321250356416⟩,
    ⟨[0, 1, 3], .prefix, 373531722108⟩,
    ⟨[0, 1, 4], .prefix, 448104406867⟩,
    ⟨[0, 2], .prefix, 261116836882⟩,
    ⟨[0, 3], .prefix, 273597133098⟩,
    ⟨[0, 4], .prefix, 307422890969⟩,
    ⟨[0, 5], .prefix, 319903187185⟩,
    ⟨[0, 6], .prefix, 409495515712⟩,
    ⟨[0, 7], .prefix, 438460259205⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .kernel, 407297307395⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 316111374181⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 307996274044⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 361328183668⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 342472161433⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 318135297020⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 324964194229⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 43 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 300033384705⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 385470353359⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 338499447247⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 365324363116⟩,
    ⟨[1, 0, 0, 1], .prefix, 316111374181⟩,
    ⟨[1, 0, 0, 2], .prefix, 353251677827⟩,
    ⟨[1, 0, 0, 3], .prefix, 626081767776⟩,
    ⟨[1, 0, 1], .prefix, 324964194229⟩,
    ⟨[1, 0, 2], .prefix, 360130378324⟩,
    ⟨[1, 0, 3], .prefix, 425799735622⟩,
    ⟨[1, 0, 4], .prefix, 495441807106⟩,
    ⟨[1, 1], .prefix, 361328183668⟩,
    ⟨[1, 2], .prefix, 390851824042⟩,
    ⟨[1, 3], .prefix, 430922244696⟩,
    ⟨[1, 4], .prefix, 469810844191⟩,
    ⟨[1, 5], .prefix, 494924883757⟩,
    ⟨[1, 6], .prefix, 667250358186⟩,
    ⟨[1, 7], .prefix, 755748451905⟩,
    ⟨[2], .prefix, 317033240393⟩,
    ⟨[3], .prefix, 338499447247⟩,
    ⟨[4], .prefix, 349765970552⟩,
    ⟨[5], .prefix, 365324363116⟩,
    ⟨[6], .prefix, 375355594160⟩,
    ⟨[7], .prefix, 557921617107⟩,
    ⟨[8], .prefix, 648185684109⟩,
    ⟨[9], .prefix, 692388834553⟩,
    ⟨[10], .prefix, 713855041407⟩,
    ⟨[11], .prefix, 725121564712⟩,
    ⟨[12], .prefix, 740679957276⟩,
    ⟨[13], .prefix, 750711188320⟩,
    ⟨[14], .prefix, 933277211267⟩,
    ⟨[15], .prefix, 1023541278269⟩,
    ⟨[16], .prefix, 1067744428713⟩,
    ⟨[17], .prefix, 1089210635567⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 43 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 43 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 43 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 43) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 43 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 43,
      hHat (residueBoxValue 43 v / 43) ≤ ((residueBoxValue 43 v / 43).divisors.card : ℚ) →
      hHat (residueBoxValue 43 v) < ((residueBoxValue 43 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP43
