/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP47
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP47.residue_step
   digest: Complete residue-tree certificate for largest prime 47. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP47

def initialVector (r : ℕ) : ℕ :=
  if r < 47 then
    if r < 23 then
      if r < 11 then
        if r < 5 then
          if r < 2 then
            if r < 1 then 0 else 193366897209
          else
            if r < 3 then
              92532684314
            else
              if r < 4 then 58990725132 else 42275463007
        else
          if r < 8 then
            if r < 6 then
              32294063701
            else
              if r < 7 then 25682507713 else 20999322292
          else
            if r < 9 then
              17524017225
            else
              if r < 10 then 14856568227 else 12757213728
      else
        if r < 17 then
          if r < 14 then
            if r < 12 then
              11073640499
            else
              if r < 13 then 9704580930 else 8580217508
          else
            if r < 15 then
              7650991600
            else
              if r < 16 then 6880895566 else 6243289195
        else
          if r < 20 then
            if r < 18 then
              5718201623
            else
              if r < 19 then 5290544064 else 4948900359
          else
            if r < 21 then
              4684695828
            else
              if r < 22 then 4491623353 else 4365248625
    else
      if r < 35 then
        if r < 29 then
          if r < 26 then
            if r < 24 then
              4302748072
            else
              if r < 25 then 4302748072 else 4365248625
          else
            if r < 27 then
              4491623353
            else
              if r < 28 then 4684695828 else 4948900359
        else
          if r < 32 then
            if r < 30 then
              5290544064
            else
              if r < 31 then 5718201623 else 6243289195
          else
            if r < 33 then
              6880895566
            else
              if r < 34 then 7650991600 else 8580217508
      else
        if r < 41 then
          if r < 38 then
            if r < 36 then
              9704580930
            else
              if r < 37 then 11073640499 else 12757213728
          else
            if r < 39 then
              14856568227
            else
              if r < 40 then 17524017225 else 20999322292
        else
          if r < 44 then
            if r < 42 then
              25682507713
            else
              if r < 43 then 32294063701 else 42275463007
          else
            if r < 45 then
              58990725132
            else
              if r < 46 then 92532684314 else 193366897209
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 219049404922⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 206124110937⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], .kernel, 199610186404⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 304337666278⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 317825378431⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 292302677642⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 201947114717⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], .kernel, 197669645281⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 345699061755⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 321286670166⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 303341491079⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 370572814368⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 302263766086⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 225660960910⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 204440537708⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 201947114717⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 230951504974⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 204440537708⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 220084421124⟩,
    ⟨[0, 0, 0, 1], .prefix, 214366219501⟩,
    ⟨[0, 0, 0, 2], .prefix, 306898903815⟩,
    ⟨[0, 0, 0, 3], .prefix, 314549895415⟩,
    ⟨[0, 0, 1], .prefix, 225660960910⟩,
    ⟨[0, 0, 2], .prefix, 230609861269⟩,
    ⟨[0, 0, 3], .prefix, 264187418266⟩,
    ⟨[0, 0, 4], .prefix, 296481481967⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 304337666278⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 317825378431⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 292302677642⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 451967808745⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 278647488697⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 370572814368⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 291532581608⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 300351286971⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 278647488697⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 317822447964⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 300351286971⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 325842232616⟩,
    ⟨[0, 1, 0, 1], .prefix, 277848567986⟩,
    ⟨[0, 1, 0, 2], .prefix, 396063760013⟩,
    ⟨[0, 1, 0, 3], .prefix, 436008815314⟩,
    ⟨[0, 1, 1], .prefix, 291532581608⟩,
    ⟨[0, 1, 2], .prefix, 369477316308⟩,
    ⟨[0, 1, 3], .prefix, 500456916996⟩,
    ⟨[0, 1, 4], .prefix, 540401972297⟩,
    ⟨[0, 2], .prefix, 267214190568⟩,
    ⟨[0, 3], .prefix, 273457479763⟩,
    ⟨[0, 4], .prefix, 284091857181⟩,
    ⟨[0, 5], .prefix, 298948425408⟩,
    ⟨[0, 6], .prefix, 348606868140⟩,
    ⟨[0, 7], .prefix, 407597593272⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 345699061755⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 321286670166⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 303341491079⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 370572814368⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 302263766086⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 678176854357⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 603629548292⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 546062413789⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 47 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 631598433406⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 520080523658⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 330950858952⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 301338470647⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 302263766086⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 347315043515⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 301338470647⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 328848314546⟩,
    ⟨[1, 0, 0, 1], .prefix, 314549895415⟩,
    ⟨[1, 0, 0, 2], .prefix, 509253244924⟩,
    ⟨[1, 0, 0, 3], .prefix, 537903558816⟩,
    ⟨[1, 0, 1], .prefix, 330950858952⟩,
    ⟨[1, 0, 2], .prefix, 394306832709⟩,
    ⟨[1, 0, 3], .prefix, 414112301295⟩,
    ⟨[1, 0, 4], .prefix, 448028657572⟩,
    ⟨[1, 1], .prefix, 370572814368⟩,
    ⟨[1, 2], .prefix, 390719926659⟩,
    ⟨[1, 3], .prefix, 420482686183⟩,
    ⟨[1, 4], .prefix, 449133000075⟩,
    ⟨[1, 5], .prefix, 469280112366⟩,
    ⟨[1, 6], .prefix, 650912737341⟩,
    ⟨[1, 7], .prefix, 714268711098⟩,
    ⟨[2], .prefix, 328175044530⟩,
    ⟨[3], .prefix, 345699061755⟩,
    ⟨[4], .prefix, 351942350950⟩,
    ⟨[5], .prefix, 384580143370⟩,
    ⟨[6], .prefix, 426855606377⟩,
    ⟨[7], .prefix, 444379623602⟩,
    ⟨[8], .prefix, 450622912797⟩,
    ⟨[9], .prefix, 459818512726⟩,
    ⟨[10], .prefix, 466061801921⟩,
    ⟨[11], .prefix, 479965625017⟩,
    ⟨[12], .prefix, 486208914212⟩,
    ⟨[13], .prefix, 508587914548⟩,
    ⟨[14], .prefix, 521345128276⟩,
    ⟨[15], .prefix, 526029824104⟩,
    ⟨[16], .prefix, 547029146396⟩,
    ⟨[17], .prefix, 563300812525⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 47 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 47 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 47 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 47) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 47 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 47,
      hHat (residueBoxValue 47 v / 47) ≤ ((residueBoxValue 47 v / 47).divisors.card : ℚ) →
      hHat (residueBoxValue 47 v) < ((residueBoxValue 47 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP47
