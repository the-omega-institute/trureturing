/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP31
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP31.residue_step
   digest: Complete residue-tree certificate for largest prime 31. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP31

def initialVector (r : ℕ) : ℕ :=
  if r < 31 then
    if r < 15 then
      if r < 7 then
        if r < 3 then
          if r < 1 then
            0
          else
            if r < 2 then 131040655043 else 64531995885
        else
          if r < 5 then
            if r < 4 then 42424246592 else 31432053312
          else
            if r < 6 then 24899121434 else 20607579270
      else
        if r < 11 then
          if r < 9 then
            if r < 8 then 17607922581 else 15426543132
          else
            if r < 10 then 13801624130 else 12577562160
        else
          if r < 13 then
            if r < 12 then 11657057553 else 10977260072
          else
            if r < 14 then 10497055285 else 10189970401
    else
      if r < 23 then
        if r < 19 then
          if r < 17 then
            if r < 16 then 10040148300 else 10040148300
          else
            if r < 18 then 10189970401 else 10497055285
        else
          if r < 21 then
            if r < 20 then 10977260072 else 11657057553
          else
            if r < 22 then 12577562160 else 13801624130
      else
        if r < 27 then
          if r < 25 then
            if r < 24 then 15426543132 else 17607922581
          else
            if r < 26 then 20607579270 else 24899121434
        else
          if r < 29 then
            if r < 28 then 31432053312 else 42424246592
          else
            if r < 30 then 64531995885 else 131040655043
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 242431247372⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 230968827647⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 199868704839⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 248186867921⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 193270258026⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 1], .prefix, 183159734041⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 230968827647⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 199868704839⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 1, 0, 1], .prefix, 455126661228⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 1, 1], .prefix, 369187264628⟩,
    ⟨[0, 0, 0, 0, 0, 1, 1], .prefix, 183159734041⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 153674972668⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 248186867921⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 193270258026⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 1], .prefix, 183159734041⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1, 0, 0, 1], .prefix, 469218200532⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1, 0, 1], .prefix, 377897079219⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1, 1], .prefix, 347331761994⟩,
    ⟨[0, 0, 0, 0, 1, 1], .prefix, 183159734041⟩,
    ⟨[0, 0, 0, 0, 1, 2], .prefix, 305402653397⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 185121959188⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 223370543910⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 222504877528⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 1], .prefix, 223677628794⟩,
    ⟨[0, 0, 0, 1, 0, 0, 1], .prefix, 219564245459⟩,
    ⟨[0, 0, 0, 1, 0, 1], .prefix, 223677628794⟩,
    ⟨[0, 0, 0, 1, 0, 2], .prefix, 258766720629⟩,
    ⟨[0, 0, 0, 1, 1], .prefix, 219564245459⟩,
    ⟨[0, 0, 0, 1, 2], .prefix, 274566054211⟩,
    ⟨[0, 0, 0, 2], .prefix, 162450201754⟩,
    ⟨[0, 0, 0, 3], .prefix, 223677628794⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 233049334522⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 200688210206⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 1], .prefix, 231449032434⟩,
    ⟨[0, 0, 1, 0, 0, 0, 1], .prefix, 194737345178⟩,
    ⟨[0, 0, 1, 0, 0, 1], .prefix, 231449032434⟩,
    ⟨[0, 0, 1, 0, 0, 2], .prefix, 284370334311⟩,
    ⟨[0, 0, 1, 0, 1], .prefix, 194737345178⟩,
    ⟨[0, 0, 1, 0, 2], .prefix, 252749386889⟩,
    ⟨[0, 0, 1, 1], .prefix, 204979752370⟩,
    ⟨[0, 0, 1, 2], .prefix, 257901054247⟩,
    ⟨[0, 0, 1, 3], .prefix, 335010612292⟩,
    ⟨[0, 0, 2], .prefix, 176547355747⟩,
    ⟨[0, 0, 3, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 3, 0, 0, 0, 0, 0, 0, 1], .prefix, 460206824792⟩,
    ⟨[0, 0, 3, 0, 0, 0, 0, 0, 1], .prefix, 399717097548⟩,
    ⟨[0, 0, 3, 0, 0, 0, 0, 1], .prefix, 406652088979⟩,
    ⟨[0, 0, 3, 0, 0, 0, 1], .prefix, 379942101789⟩,
    ⟨[0, 0, 3, 0, 0, 1], .prefix, 406652088979⟩,
    ⟨[0, 0, 3, 0, 0, 2], .prefix, 480110594441⟩,
    ⟨[0, 0, 3, 0, 1], .prefix, 379942101789⟩,
    ⟨[0, 0, 3, 0, 2], .prefix, 485327798558⟩,
    ⟨[0, 0, 3, 1], .prefix, 385892966817⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 31 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[0, 0, 3, 2], .prefix, 459871850772⟩,
    ⟨[0, 0, 3, 3], .prefix, 611970286281⟩,
    ⟨[0, 0, 4], .prefix, 332487132224⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 258604476790⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 215874215019⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 209341283141⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 249653955073⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 209341283141⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 285530336579⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 249653955073⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 338930146792⟩,
    ⟨[0, 1, 0, 1], .prefix, 218698579077⟩,
    ⟨[0, 1, 0, 2], .prefix, 254574960583⟩,
    ⟨[0, 1, 0, 3], .prefix, 314713559948⟩,
    ⟨[0, 1, 1], .prefix, 228757792358⟩,
    ⟨[0, 1, 2], .prefix, 264634173864⟩,
    ⟨[0, 1, 3], .prefix, 412973707559⟩,
    ⟨[0, 1, 4], .prefix, 493391966222⟩,
    ⟨[0, 2], .prefix, 187266525765⟩,
    ⟨[0, 3], .prefix, 218698579077⟩,
    ⟨[0, 4], .prefix, 231276141237⟩,
    ⟨[0, 5], .prefix, 254574960583⟩,
    ⟨[0, 6], .prefix, 272289313356⟩,
    ⟨[0, 7], .prefix, 314713559948⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 242431247372⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 230968827647⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 248186867921⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 230968827647⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 283583044640⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 248186867921⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 284063158473⟩,
    ⟨[1, 0, 0, 1], .prefix, 223370543910⟩,
    ⟨[1, 0, 0, 2], .prefix, 258766720629⟩,
    ⟨[1, 0, 0, 3], .prefix, 389537316339⟩,
    ⟨[1, 0, 1], .prefix, 233049334522⟩,
    ⟨[1, 0, 2], .prefix, 264634173864⟩,
    ⟨[1, 0, 3], .prefix, 460206824792⟩,
    ⟨[1, 0, 4], .prefix, 497683508386⟩,
    ⟨[1, 1], .prefix, 258604476790⟩,
    ⟨[1, 2], .prefix, 282903156205⟩,
    ⟨[1, 3], .prefix, 329761752649⟩,
    ⟨[1, 4], .prefix, 358346935302⟩,
    ⟨[1, 5], .prefix, 395823618896⟩,
    ⟨[1, 6], .prefix, 536904422239⟩,
    ⟨[1, 7], .prefix, 589518639232⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 0, 1], .kernel, 338395296569⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 383512050715⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 1], .prefix, 274978443119⟩,
    ⟨[2, 0, 0, 0, 0, 0, 1], .prefix, 300226500503⟩,
    ⟨[2, 0, 0, 0, 0, 1], .prefix, 274978443119⟩,
    ⟨[2, 0, 0, 0, 0, 2], .prefix, 348200239382⟩,
    ⟨[2, 0, 0, 0, 1], .prefix, 300226500503⟩,
    ⟨[2, 0, 0, 0, 2], .prefix, 338262744346⟩,
    ⟨[2, 0, 0, 1], .prefix, 297226843814⟩,
    ⟨[2, 0, 0, 2], .prefix, 346424644663⟩,
    ⟨[2, 0, 0, 3], .prefix, 520590457371⟩,
    ⟨[2, 0, 1], .prefix, 279621885162⟩,
    ⟨[2, 0, 2], .prefix, 327595624041⟩,
    ⟨[2, 0, 3], .prefix, 552335911550⟩,
    ⟨[2, 0, 4], .prefix, 607217509203⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 31 2 4294967296 initialVector) = true := by
  decide +kernel

private def block2 : List ResidueTerminal :=
  [
    ⟨[2, 1], .prefix, 301013790174⟩,
    ⟨[2, 2], .prefix, 350211591023⟩,
    ⟨[2, 3], .prefix, 491770434132⟩,
    ⟨[2, 4], .prefix, 565779520066⟩,
    ⟨[2, 5], .prefix, 614977320915⟩,
    ⟨[2, 6], .prefix, 700632029196⟩,
    ⟨[2, 7], .prefix, 774336613197⟩,
    ⟨[3], .prefix, 242431247372⟩,
    ⟨[4], .prefix, 252471395672⟩,
    ⟨[5], .prefix, 383512050715⟩,
    ⟨[6], .prefix, 448044046600⟩,
    ⟨[7], .prefix, 479476099912⟩,
    ⟨[8], .prefix, 494902643044⟩,
    ⟨[9], .prefix, 504942791344⟩,
    ⟨[10], .prefix, 635983446387⟩,
    ⟨[11], .prefix, 700515442272⟩,
    ⟨[12], .prefix, 731947495584⟩,
    ⟨[13], .prefix, 747374038716⟩,
    ⟨[14], .prefix, 757414187016⟩,
    ⟨[15], .prefix, 888454842059⟩,
    ⟨[16], .prefix, 952986837944⟩,
    ⟨[17], .prefix, 984418891256⟩
  ]

private theorem checked2 :
    block2.all (checkResidueTerminal 31 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1 ++ block2

private theorem all_checked :
    certificates.all (checkResidueTerminal 31 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, checked2, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 31 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 31) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 31 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 31,
      hHat (residueBoxValue 31 v / 31) ≤ ((residueBoxValue 31 v / 31).divisors.card : ℚ) →
      hHat (residueBoxValue 31 v) < ((residueBoxValue 31 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP31
