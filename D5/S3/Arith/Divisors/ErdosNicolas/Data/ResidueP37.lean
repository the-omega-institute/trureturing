/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP37
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP37.residue_step
   digest: Complete residue-tree certificate for largest prime 37. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP37

def initialVector (r : ℕ) : ℕ :=
  if r < 37 then
    if r < 18 then
      if r < 9 then
        if r < 4 then
          if r < 2 then
            if r < 1 then 0 else 156802003165
          else
            if r < 3 then 77394235679 else 50971363667
        else
          if r < 6 then
            if r < 5 then 37805258137 else 29950672178
          else
            if r < 7 then
              24759618169
            else
              if r < 8 then 21097719178 else 18398310030
      else
        if r < 13 then
          if r < 11 then
            if r < 10 then 16347153610 else 14756345492
          else
            if r < 12 then 13507020290 else 12520729827
        else
          if r < 15 then
            if r < 14 then 11744063641 else 11139898263
          else
            if r < 16 then
              10682193426
            else
              if r < 17 then 10352799705 else 10139466881
    else
      if r < 27 then
        if r < 22 then
          if r < 20 then
            if r < 19 then 10034613654 else 10034613654
          else
            if r < 21 then 10139466881 else 10352799705
        else
          if r < 24 then
            if r < 23 then 10682193426 else 11139898263
          else
            if r < 25 then
              11744063641
            else
              if r < 26 then 12520729827 else 13507020290
      else
        if r < 32 then
          if r < 29 then
            if r < 28 then 14756345492 else 16347153610
          else
            if r < 30 then
              18398310030
            else
              if r < 31 then 21097719178 else 24759618169
        else
          if r < 34 then
            if r < 33 then 29950672178 else 37805258137
          else
            if r < 35 then
              50971363667
            else
              if r < 36 then 77394235679 else 156802003165
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 175200313195⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 175200313195⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], .kernel, 166836616819⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 271476586840⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 262947348579⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 262947348579⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 168546066806⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 168546066806⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 188039189224⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 171558348657⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 185065368947⟩,
    ⟨[0, 0, 0, 1], .prefix, 177899722343⟩,
    ⟨[0, 0, 0, 2], .prefix, 218126166537⟩,
    ⟨[0, 0, 0, 3], .prefix, 239223885715⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 232610012690⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 256122349040⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 256122349040⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 1], .prefix, 278903256514⟩,
    ⟨[0, 0, 1, 0, 0, 0, 1], .prefix, 215428921609⟩,
    ⟨[0, 0, 1, 0, 0, 1], .prefix, 215428921609⟩,
    ⟨[0, 0, 1, 0, 0, 2], .prefix, 308891117371⟩,
    ⟨[0, 0, 1, 0, 1], .prefix, 259634777762⟩,
    ⟨[0, 0, 1, 0, 2], .prefix, 283281264933⟩,
    ⟨[0, 0, 1, 1], .prefix, 285244630200⟩,
    ⟨[0, 0, 1, 2], .prefix, 320357048074⟩,
    ⟨[0, 0, 1, 3], .prefix, 382010605167⟩,
    ⟨[0, 0, 2], .prefix, 218455560258⟩,
    ⟨[0, 0, 3], .prefix, 248406232436⟩,
    ⟨[0, 0, 4], .prefix, 266804542466⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 271476586840⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 248863937273⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 248863937273⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 309927220680⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 296911666152⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 296911666152⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 320771486147⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 259085645259⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 294939709929⟩,
    ⟨[0, 1, 0, 1], .prefix, 239223885715⟩,
    ⟨[0, 1, 0, 2], .prefix, 408546618707⟩,
    ⟨[0, 1, 0, 3], .prefix, 444400683377⟩,
    ⟨[0, 1, 1], .prefix, 248406232436⟩,
    ⟨[0, 1, 2], .prefix, 417728965428⟩,
    ⟨[0, 1, 3], .prefix, 458819535869⟩,
    ⟨[0, 1, 4], .prefix, 514127986161⟩,
    ⟨[0, 2], .prefix, 224120520442⟩,
    ⟨[0, 3], .prefix, 258099354796⟩,
    ⟨[0, 4], .prefix, 274446508406⟩,
    ⟨[0, 5], .prefix, 289202853898⟩,
    ⟨[0, 6], .prefix, 310300573076⟩,
    ⟨[0, 7], .prefix, 323807593366⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 271476586840⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 262947348579⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 262947348579⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 514044185495⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 485987533565⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 485987533565⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 295307069392⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 37 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 295307069392⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 327544686833⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 259092051217⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 283281264933⟩,
    ⟨[1, 0, 0, 1], .prefix, 274499710727⟩,
    ⟨[1, 0, 0, 2], .prefix, 350230692563⟩,
    ⟨[1, 0, 0, 3], .prefix, 382468310004⟩,
    ⟨[1, 0, 1], .prefix, 278903256514⟩,
    ⟨[1, 0, 2], .prefix, 341707133284⟩,
    ⟨[1, 0, 3], .prefix, 386414150954⟩,
    ⟨[1, 0, 4], .prefix, 415165260689⟩,
    ⟨[1, 1], .prefix, 309927220680⟩,
    ⟨[1, 2], .prefix, 336308987944⟩,
    ⟨[1, 3], .prefix, 390395582315⟩,
    ⟨[1, 4], .prefix, 416777349579⟩,
    ⟨[1, 5], .prefix, 454888267914⟩,
    ⟨[1, 6], .prefix, 487125885355⟩,
    ⟨[1, 7], .prefix, 514214251276⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 332482564161⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 330703278894⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 330703278894⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 1], .prefix, 516232349479⟩,
    ⟨[2, 0, 0, 0, 0, 0, 1], .prefix, 357871945698⟩,
    ⟨[2, 0, 0, 0, 0, 1], .prefix, 357871945698⟩,
    ⟨[2, 0, 0, 0, 0, 2], .prefix, 406456716749⟩,
    ⟨[2, 0, 0, 0, 1], .prefix, 347868673021⟩,
    ⟨[2, 0, 0, 0, 2], .prefix, 393155605915⟩,
    ⟨[2, 0, 0, 1], .prefix, 327061314356⟩,
    ⟨[2, 0, 0, 2], .prefix, 415313026019⟩,
    ⟨[2, 0, 0, 3], .prefix, 463897797070⟩,
    ⟨[2, 0, 1], .prefix, 326847981532⟩,
    ⟨[2, 0, 2], .prefix, 403173019511⟩,
    ⟨[2, 0, 3], .prefix, 461874801424⟩,
    ⟨[2, 0, 4], .prefix, 645058571853⟩,
    ⟨[2, 1], .prefix, 360253208644⟩,
    ⟨[2, 2], .prefix, 543436979073⟩,
    ⟨[2, 3], .prefix, 619304155113⟩,
    ⟨[2, 4], .prefix, 667888926164⟩,
    ⟨[2, 5], .prefix, 723632336743⟩,
    ⟨[2, 6], .prefix, 772217107794⟩,
    ⟨[2, 7], .prefix, 834792044305⟩,
    ⟨[3], .prefix, 290399807011⟩,
    ⟨[4], .prefix, 300752606716⟩,
    ⟨[5], .prefix, 330703278894⟩,
    ⟨[6], .prefix, 345459624386⟩,
    ⟨[7], .prefix, 357085046158⟩,
    ⟨[8], .prefix, 406570454934⟩,
    ⟨[9], .prefix, 431330073103⟩,
    ⟨[10], .prefix, 443850802930⟩,
    ⟨[11], .prefix, 457711840367⟩,
    ⟨[12], .prefix, 470232570194⟩,
    ⟨[13], .prefix, 489949457808⟩,
    ⟨[14], .prefix, 502470187635⟩,
    ⟨[15], .prefix, 514214251276⟩,
    ⟨[16], .prefix, 528368851338⟩,
    ⟨[17], .prefix, 538403464992⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 37 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 37 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 37 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 37) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 37 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 37,
      hHat (residueBoxValue 37 v / 37) ≤ ((residueBoxValue 37 v / 37).divisors.card : ℚ) →
      hHat (residueBoxValue 37 v) < ((residueBoxValue 37 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP37
