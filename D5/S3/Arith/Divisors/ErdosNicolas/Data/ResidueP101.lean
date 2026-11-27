/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP101
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP101.residue_step
   digest: Complete residue-tree certificate for largest prime 101. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP101

def initialVector (r : ℕ) : ℕ :=
  if r < 101 then
    if r < 50 then
      if r < 25 then
        if r < 12 then
          if r < 6 then
            if r < 3 then
              if r < 1 then
                0
              else
                if r < 2 then 431655739501 else 214773209418
            else
              if r < 4 then
                142489708289
              else
                if r < 5 then 106357318556 else 84686464040
          else
            if r < 9 then
              if r < 7 then
                70247293859
              else
                if r < 8 then 59941308601 else 52219267246
            else
              if r < 10 then
                46220489204
              else
                if r < 11 then 41428574807 else 37514915707
        else
          if r < 18 then
            if r < 15 then
              if r < 13 then
                34260449267
              else
                if r < 14 then 31513525906 else 29165835345
            else
              if r < 16 then
                27137959668
              else
                if r < 17 then 25370345942 else 23817464680
          else
            if r < 21 then
              if r < 19 then
                22443914978
              else
                if r < 20 then 21221760135 else 20128662385
            else
              if r < 23 then
                if r < 22 then 19146550909 else 18260652538
              else
                if r < 24 then 17458776370 else 16730776349
      else
        if r < 37 then
          if r < 31 then
            if r < 28 then
              if r < 26 then
                16068143427
              else
                if r < 27 then 15463691858 else 14911314677
            else
              if r < 29 then
                14405793113
              else
                if r < 30 then 13942642968 else 13517995538
          else
            if r < 34 then
              if r < 32 then
                13128497421
              else
                if r < 33 then 12771232545 else 12443657124
            else
              if r < 35 then
                12143545825
              else
                if r < 36 then 11868948237 else 11618151804
        else
          if r < 43 then
            if r < 40 then
              if r < 38 then
                11389652131
              else
                if r < 39 then 11182126724 else 10994413477
            else
              if r < 41 then
                10825493300
              else
                if r < 42 then 10674474666 else 10540580178
          else
            if r < 46 then
              if r < 44 then
                10423136469
              else
                if r < 45 then 10321565213 else 10235374540
            else
              if r < 48 then
                if r < 47 then 10164154289 else 10107569544
              else
                if r < 49 then 10065357200 else 10037322529
    else
      if r < 75 then
        if r < 62 then
          if r < 56 then
            if r < 53 then
              if r < 51 then
                10023337261
              else
                if r < 52 then 10023337261 else 10037322529
            else
              if r < 54 then
                10065357200
              else
                if r < 55 then 10107569544 else 10164154289
          else
            if r < 59 then
              if r < 57 then
                10235374540
              else
                if r < 58 then 10321565213 else 10423136469
            else
              if r < 60 then
                10540580178
              else
                if r < 61 then 10674474666 else 10825493300
        else
          if r < 68 then
            if r < 65 then
              if r < 63 then
                10994413477
              else
                if r < 64 then 11182126724 else 11389652131
            else
              if r < 66 then
                11618151804
              else
                if r < 67 then 11868948237 else 12143545825
          else
            if r < 71 then
              if r < 69 then
                12443657124
              else
                if r < 70 then 12771232545 else 13128497421
            else
              if r < 73 then
                if r < 72 then 13517995538 else 13942642968
              else
                if r < 74 then 14405793113 else 14911314677
      else
        if r < 88 then
          if r < 81 then
            if r < 78 then
              if r < 76 then
                15463691858
              else
                if r < 77 then 16068143427 else 16730776349
            else
              if r < 79 then
                17458776370
              else
                if r < 80 then 18260652538 else 19146550909
          else
            if r < 84 then
              if r < 82 then
                20128662385
              else
                if r < 83 then 21221760135 else 22443914978
            else
              if r < 86 then
                if r < 85 then 23817464680 else 25370345942
              else
                if r < 87 then 27137959668 else 29165835345
        else
          if r < 94 then
            if r < 91 then
              if r < 89 then
                31513525906
              else
                if r < 90 then 34260449267 else 37514915707
            else
              if r < 92 then
                41428574807
              else
                if r < 93 then 46220489204 else 52219267246
          else
            if r < 97 then
              if r < 95 then
                59941308601
              else
                if r < 96 then 70247293859 else 84686464040
            else
              if r < 99 then
                if r < 98 then 106357318556 else 142489708289
              else
                if r < 100 then 214773209418 else 431655739501
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      .prefix, 538013058057⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      .prefix, 465916188768⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 454099654479⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 449916392039⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 454099654479⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 445173735039⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 574145447790⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 442481232801⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 465916188768⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 442481232801⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 442078875970⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 442078875970⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 444426972046⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 445173735039⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 463169265407⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 491597048102⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 449916392039⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 457026085443⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 501903033360⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 463169265407⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 476297762828⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 469170655208⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 526506357830⟩,
    ⟨[0, 0, 0, 1], .prefix, 491597048102⟩,
    ⟨[0, 0, 0, 2], .prefix, 505539691070⟩,
    ⟨[0, 0, 0, 3], .prefix, 517983348194⟩,
    ⟨[0, 0, 1], .prefix, 516342203541⟩,
    ⟨[0, 0, 2], .prefix, 558141720442⟩,
    ⟨[0, 0, 3], .prefix, 642828184482⟩,
    ⟨[0, 0, 4], .prefix, 661974735391⟩,
    ⟨[0, 1], .prefix, 574145447790⟩,
    ⟨[0, 2], .prefix, 620365936994⟩,
    ⟨[0, 3], .prefix, 635277251671⟩,
    ⟨[0, 4], .prefix, 655405914056⟩,
    ⟨[0, 5], .prefix, 708348791863⟩,
    ⟨[0, 6], .prefix, 754569281067⟩,
    ⟨[0, 7], .prefix, 769480595744⟩,
    ⟨[1], .prefix, 646428948919⟩,
    ⟨[2], .prefix, 752786267475⟩,
    ⟨[3], .prefix, 805005534721⟩,
    ⟨[4], .prefix, 830375880663⟩,
    ⟨[5], .prefix, 843147113208⟩,
    ⟨[6], .prefix, 856467361351⟩,
    ⟨[7], .prefix, 869448080016⟩,
    ⟨[8], .prefix, 888871248210⟩,
    ⟨[9], .prefix, 939496958161⟩,
    ⟨[10], .prefix, 968662793506⟩,
    ⟨[11], .prefix, 983068586619⟩,
    ⟨[12], .prefix, 994754274194⟩,
    ⟨[13], .prefix, 1030818876866⟩,
    ⟨[14], .prefix, 1049079529404⟩,
    ⟨[15], .prefix, 1059401094617⟩,
    ⟨[16], .prefix, 1090914620523⟩,
    ⟨[17], .prefix, 1106378312381⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 101 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0

private theorem all_checked :
    certificates.all (checkResidueTerminal 101 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 101 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 101) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 101 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 101,
      hHat (residueBoxValue 101 v / 101) ≤ ((residueBoxValue 101 v / 101).divisors.card : ℚ) →
      hHat (residueBoxValue 101 v) < ((residueBoxValue 101 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP101
