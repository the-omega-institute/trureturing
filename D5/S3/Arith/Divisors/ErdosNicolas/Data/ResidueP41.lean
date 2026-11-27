/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP41
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP41.residue_step
   digest: Complete residue-tree certificate for largest prime 41. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP41

def initialVector (r : ℕ) : ℕ :=
  if r < 41 then
    if r < 20 then
      if r < 10 then
        if r < 5 then
          if r < 2 then
            if r < 1 then 0 else 173977800766
          else
            if r < 3 then
              85973521900
            else
              if r < 4 then 56678190543 else 42068604496
        else
          if r < 7 then
            if r < 6 then 33340374272 else 27558984198
          else
            if r < 8 then
              23467093834
            else
              if r < 9 then 20436369242 else 18118102224
      else
        if r < 15 then
          if r < 12 then
            if r < 11 then 16303466865 else 14860010205
          else
            if r < 13 then
              13699910490
            else
              if r < 14 then 12762899237 else 12006519593
        else
          if r < 17 then
            if r < 16 then 11400301711 else 10922146427
          else
            if r < 18 then
              10556015320
            else
              if r < 19 then 10290426996 else 10117474564
    else
      if r < 30 then
        if r < 25 then
          if r < 22 then
            if r < 21 then 10032195097 else 10032195097
          else
            if r < 23 then
              10117474564
            else
              if r < 24 then 10290426996 else 10556015320
        else
          if r < 27 then
            if r < 26 then 10922146427 else 11400301711
          else
            if r < 28 then
              12006519593
            else
              if r < 29 then 12762899237 else 13699910490
      else
        if r < 35 then
          if r < 32 then
            if r < 31 then 14860010205 else 16303466865
          else
            if r < 33 then
              18118102224
            else
              if r < 34 then 20436369242 else 23467093834
        else
          if r < 38 then
            if r < 36 then
              27558984198
            else
              if r < 37 then 33340374272 else 42068604496
          else
            if r < 39 then
              56678190543
            else
              if r < 40 then 85973521900 else 173977800766
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], .kernel, 190281267631⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 406327672893⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 187677711256⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 184899947193⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 186740700003⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 187677711256⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 186740700003⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 220081074275⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 188837810971⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 274811332871⟩,
    ⟨[0, 0, 0, 1], .prefix, 201536784964⟩,
    ⟨[0, 0, 0, 2], .prefix, 234877159236⟩,
    ⟨[0, 0, 0, 3], .prefix, 258344253070⟩,
    ⟨[0, 0, 1], .prefix, 207318175038⟩,
    ⟨[0, 0, 2], .prefix, 227754544280⟩,
    ⟨[0, 0, 3], .prefix, 304213843365⟩,
    ⟨[0, 0, 4], .prefix, 324650212607⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 286424506295⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 286424506295⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 277696276071⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 265045231570⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 329392412446⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 277696276071⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 329392412446⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 374133088429⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 284124897516⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 379484876854⟩,
    ⟨[0, 1, 0, 1], .prefix, 299516826457⟩,
    ⟨[0, 1, 0, 2], .prefix, 346557111219⟩,
    ⟨[0, 1, 0, 3], .prefix, 380946351480⟩,
    ⟨[0, 1, 1], .prefix, 275396667292⟩,
    ⟨[0, 1, 2], .prefix, 309785907553⟩,
    ⟨[0, 1, 3], .prefix, 423318413651⟩,
    ⟨[0, 1, 4], .prefix, 454481890721⟩,
    ⟨[0, 2], .prefix, 248774093533⟩,
    ⟨[0, 3], .prefix, 260780613126⟩,
    ⟨[0, 4], .prefix, 434758413892⟩,
    ⟨[0, 5], .prefix, 491436604435⟩,
    ⟨[0, 6], .prefix, 509554706659⟩,
    ⟨[0, 7], .prefix, 521561226252⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 322456296404⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 322456296404⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 293974431820⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 303582123934⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 326746987773⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 293974431820⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 326746987773⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 358105503442⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 286211634582⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 470221630445⟩,
    ⟨[1, 0, 0, 1], .prefix, 301210217354⟩,
    ⟨[1, 0, 0, 2], .prefix, 350854058491⟩,
    ⟨[1, 0, 0, 3], .prefix, 386327671918⟩,
    ⟨[1, 0, 1], .prefix, 309595163803⟩,
    ⟨[1, 0, 2], .prefix, 340953679472⟩,
    ⟨[1, 0, 3], .prefix, 518950635466⟩,
    ⟨[1, 0, 4], .prefix, 581455609204⟩,
    ⟨[1, 1], .prefix, 344188497407⟩,
    ⟨[1, 2], .prefix, 372597026627⟩,
    ⟨[1, 3], .prefix, 397366445457⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 41 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 4], .prefix, 657317768123⟩,
    ⟨[1, 5], .prefix, 741554942864⟩,
    ⟨[1, 6], .prefix, 769963472084⟩,
    ⟨[1, 7], .prefix, 794732890914⟩,
    ⟨[2], .prefix, 302019927162⟩,
    ⟨[3], .prefix, 322456296404⟩,
    ⟨[4], .prefix, 333378442831⟩,
    ⟨[5], .prefix, 361695963396⟩,
    ⟨[6], .prefix, 382132332638⟩,
    ⟨[7], .prefix, 395127346323⟩,
    ⟨[8], .prefix, 411430813188⟩,
    ⟨[9], .prefix, 421463008285⟩,
    ⟨[10], .prefix, 595440809051⟩,
    ⟨[11], .prefix, 681414330951⟩,
    ⟨[12], .prefix, 723482935447⟩,
    ⟨[13], .prefix, 743919304689⟩,
    ⟨[14], .prefix, 754841451116⟩,
    ⟨[15], .prefix, 783158971681⟩,
    ⟨[16], .prefix, 803595340923⟩,
    ⟨[17], .prefix, 816590354608⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 41 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 41 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 41 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 41) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 41 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 41,
      hHat (residueBoxValue 41 v / 41) ≤ ((residueBoxValue 41 v / 41).divisors.card : ℚ) →
      hHat (residueBoxValue 41 v) < ((residueBoxValue 41 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP41
