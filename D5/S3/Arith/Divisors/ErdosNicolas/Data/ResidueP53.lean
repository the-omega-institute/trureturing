/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP53
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP53.residue_step
   digest: Complete residue-tree certificate for largest prime 53. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP53

def initialVector (r : ℕ) : ℕ :=
  if r < 53 then
    if r < 26 then
      if r < 13 then
        if r < 6 then
          if r < 3 then
            if r < 1 then
              0
            else
              if r < 2 then 219125927625 else 105395128894
          else
            if r < 4 then
              67545519048
            else
              if r < 5 then 48668991666 else 37384111250
        else
          if r < 9 then
            if r < 7 then
              29897236910
            else
              if r < 8 then 24582685548 else 20627773502
          else
            if r < 11 then
              if r < 10 then 17581166711 else 15172221735
            else
              if r < 12 then 13228871212 else 11636567938
      else
        if r < 19 then
          if r < 16 then
            if r < 14 then
              10316181111
            else
              if r < 15 then 9211367650 else 8280998442
          else
            if r < 17 then
              7494427774
            else
              if r < 18 then 6828436664 else 6265198403
        else
          if r < 22 then
            if r < 20 then
              5790892499
            else
              if r < 21 then 5394739282 else 5068317105
          else
            if r < 24 then
              if r < 23 then 4805073472 else 4599972270
            else
              if r < 25 then 4449240588 else 4350188358
    else
      if r < 39 then
        if r < 32 then
          if r < 29 then
            if r < 27 then
              4301085501
            else
              if r < 28 then 4301085501 else 4350188358
          else
            if r < 30 then
              4449240588
            else
              if r < 31 then 4599972270 else 4805073472
        else
          if r < 35 then
            if r < 33 then
              5068317105
            else
              if r < 34 then 5394739282 else 5790892499
          else
            if r < 37 then
              if r < 36 then 6265198403 else 6828436664
            else
              if r < 38 then 7494427774 else 8280998442
      else
        if r < 46 then
          if r < 42 then
            if r < 40 then
              9211367650
            else
              if r < 41 then 10316181111 else 11636567938
          else
            if r < 44 then
              if r < 43 then 13228871212 else 15172221735
            else
              if r < 45 then 17581166711 else 20627773502
        else
          if r < 49 then
            if r < 47 then
              24582685548
            else
              if r < 48 then 29897236910 else 37384111250
          else
            if r < 51 then
              if r < 50 then 48668991666 else 67545519048
            else
              if r < 52 then 105395128894 else 219125927625
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 249023164535⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 234298149360⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 230762495563⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 234298149360⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 230762495563⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 232354798837⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 223725899895⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 228337295275⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 225954364289⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 267794919291⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 278111100402⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 232354798837⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 248157853761⟩,
    ⟨[0, 0, 0, 1], .prefix, 243708613173⟩,
    ⟨[0, 0, 0, 2], .prefix, 292377604839⟩,
    ⟨[0, 0, 0, 3], .prefix, 300658603281⟩,
    ⟨[0, 0, 1], .prefix, 256510038875⟩,
    ⟨[0, 0, 2], .prefix, 261578355980⟩,
    ⟨[0, 0, 3], .prefix, 268406792644⟩,
    ⟨[0, 0, 4], .prefix, 279879990944⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 360683491832⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 331549985697⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 305136451275⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 331549985697⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 305136451275⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 305295057167⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0, 1], .prefix, 298765846717⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 341131330838⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 398895012231⟩,
    ⟨[0, 1, 0, 0, 0, 1], .prefix, 346977006277⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 391855545301⟩,
    ⟨[0, 1, 0, 0, 1], .prefix, 305295057167⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 334203829111⟩,
    ⟨[0, 1, 0, 1], .prefix, 316322449326⟩,
    ⟨[0, 1, 0, 2], .prefix, 376628008930⟩,
    ⟨[0, 1, 0, 3], .prefix, 447331332936⟩,
    ⟨[0, 1, 1], .prefix, 332336556365⟩,
    ⟨[0, 1, 2], .prefix, 419135551071⟩,
    ⟨[0, 1, 3], .prefix, 464800660763⟩,
    ⟨[0, 1, 4], .prefix, 487240899625⟩,
    ⟨[0, 2], .prefix, 304252613384⟩,
    ⟨[0, 3], .prefix, 360683491832⟩,
    ⟨[0, 4], .prefix, 428229010880⟩,
    ⟨[0, 5], .prefix, 445810177591⟩,
    ⟨[0, 6], .prefix, 452638614255⟩,
    ⟨[0, 7], .prefix, 495363007148⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 366054861367⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 345088017536⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 346907296702⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 345088017536⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 346907296702⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 366354408357⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 353703714337⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 338592947460⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 396416763925⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 393817821687⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 408435088299⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 366354408357⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 400148461555⟩,
    ⟨[1, 0, 0, 1], .prefix, 358315109717⟩,
    ⟨[1, 0, 0, 2], .prefix, 427611874885⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 53 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 3], .prefix, 499507582291⟩,
    ⟨[1, 0, 1], .prefix, 377077389504⟩,
    ⟨[1, 0, 2], .prefix, 448973096910⟩,
    ⟨[1, 0, 3], .prefix, 467270285227⟩,
    ⟨[1, 0, 4], .prefix, 481342176168⟩,
    ⟨[1, 1], .prefix, 421963812477⟩,
    ⟨[1, 2], .prefix, 445810177591⟩,
    ⟨[1, 3], .prefix, 669237190717⟩,
    ⟨[1, 4], .prefix, 741132898123⟩,
    ⟨[1, 5], .prefix, 763519138306⟩,
    ⟨[1, 6], .prefix, 877928751192⟩,
    ⟨[1, 7], .prefix, 949824458598⟩,
    ⟨[2], .prefix, 373190048185⟩,
    ⟨[3], .prefix, 393817821687⟩,
    ⟨[4], .prefix, 401312249461⟩,
    ⟨[5], .prefix, 408435088299⟩,
    ⟨[6], .prefix, 419609437778⟩,
    ⟨[7], .prefix, 445758387064⟩,
    ⟨[8], .prefix, 466386160566⟩,
    ⟨[9], .prefix, 473880588340⟩,
    ⟨[10], .prefix, 510617959882⟩,
    ⟨[11], .prefix, 559286951548⟩,
    ⟨[12], .prefix, 579914725050⟩,
    ⟨[13], .prefix, 587409152824⟩,
    ⟨[14], .prefix, 597431193104⟩,
    ⟨[15], .prefix, 618058966606⟩,
    ⟨[16], .prefix, 625553394380⟩,
    ⟨[17], .prefix, 630939937318⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 53 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 53 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 53 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 53) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 53 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 53,
      hHat (residueBoxValue 53 v / 53) ≤ ((residueBoxValue 53 v / 53).divisors.card : ℚ) →
      hHat (residueBoxValue 53 v) < ((residueBoxValue 53 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP53
