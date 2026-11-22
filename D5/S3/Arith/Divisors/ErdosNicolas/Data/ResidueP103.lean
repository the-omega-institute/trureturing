/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP103
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP103.residue_step
   digest: Complete residue-tree certificate for largest prime 103. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP103

def initialVector (r : ℕ) : ℕ :=
  if r < 103 then
    if r < 51 then
      if r < 25 then
        if r < 12 then
          if r < 6 then
            if r < 3 then
              if r < 1 then
                0
              else
                if r < 2 then 440245433238 else 219067625982
            else
              if r < 4 then
                145352089934
              else
                if r < 5 then 108503423402 else 86402552722
          else
            if r < 9 then
              if r < 7 then
                71676460824
              else
                if r < 8 then 61165290739 else 53289121862
            else
              if r < 10 then
                47170228569
              else
                if r < 11 then 42281984117 else 38289270693
        else
          if r < 18 then
            if r < 15 then
              if r < 13 then
                34968685314
              else
                if r < 14 then 32165573583 else 29769477064
            else
              if r < 16 then
                27699402119
              else
                if r < 17 then 25894613768 else 24308676933
          else
            if r < 21 then
              if r < 19 then
                22905485788
              else
                if r < 20 then 21656546207 else 20539073560
            else
              if r < 23 then
                if r < 22 then 19534634143 else 18628156996
              else
                if r < 24 then 17807204045 else 17061422039
      else
        if r < 38 then
          if r < 31 then
            if r < 28 then
              if r < 26 then
                16382126842
              else
                if r < 27 then 15761983206 else 15194755408
            else
              if r < 29 then
                14675113095
              else
                if r < 30 then 14198474724 else 13760884786
          else
            if r < 34 then
              if r < 32 then
                13358913381
              else
                if r < 33 then 12989575672 else 12650265244
            else
              if r < 36 then
                if r < 35 then 12338700029 else 12052876780
              else
                if r < 37 then 11791034506 else 11551622233
        else
          if r < 44 then
            if r < 41 then
              if r < 39 then
                11333273769
              else
                if r < 40 then 11134785456 else 10955097218
            else
              if r < 42 then
                10793277214
              else
                if r < 43 then 10648508963 else 10520079396
          else
            if r < 47 then
              if r < 45 then
                10407369689
              else
                if r < 46 then 10309847847 else 10227060979
            else
              if r < 49 then
                if r < 48 then 10158630663 else 10104248208
              else
                if r < 50 then 10063670122 else 10036716979
    else
      if r < 77 then
        if r < 64 then
          if r < 57 then
            if r < 54 then
              if r < 52 then
                10023270123
              else
                if r < 53 then 10023270123 else 10036716979
            else
              if r < 55 then
                10063670122
              else
                if r < 56 then 10104248208 else 10158630663
          else
            if r < 60 then
              if r < 58 then
                10227060979
              else
                if r < 59 then 10309847847 else 10407369689
            else
              if r < 62 then
                if r < 61 then 10520079396 else 10648508963
              else
                if r < 63 then 10793277214 else 10955097218
        else
          if r < 70 then
            if r < 67 then
              if r < 65 then
                11134785456
              else
                if r < 66 then 11333273769 else 11551622233
            else
              if r < 68 then
                11791034506
              else
                if r < 69 then 12052876780 else 12338700029
          else
            if r < 73 then
              if r < 71 then
                12650265244
              else
                if r < 72 then 12989575672 else 13358913381
            else
              if r < 75 then
                if r < 74 then 13760884786 else 14198474724
              else
                if r < 76 then 14675113095 else 15194755408
      else
        if r < 90 then
          if r < 83 then
            if r < 80 then
              if r < 78 then
                15761983206
              else
                if r < 79 then 16382126842 else 17061422039
            else
              if r < 81 then
                17807204045
              else
                if r < 82 then 18628156996 else 19534634143
          else
            if r < 86 then
              if r < 84 then
                20539073560
              else
                if r < 85 then 21656546207 else 22905485788
            else
              if r < 88 then
                if r < 87 then 24308676933 else 25894613768
              else
                if r < 89 then 27699402119 else 29769477064
        else
          if r < 96 then
            if r < 93 then
              if r < 91 then
                32165573583
              else
                if r < 92 then 34968685314 else 38289270693
            else
              if r < 94 then
                42281984117
              else
                if r < 95 then 47170228569 else 53289121862
          else
            if r < 99 then
              if r < 97 then
                61165290739
              else
                if r < 98 then 71676460824 else 86402552722
            else
              if r < 101 then
                if r < 100 then 108503423402 else 145352089934
              else
                if r < 102 then 219067625982 else 440245433238
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      .prefix, 659313059220⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      .prefix, 511921894062⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      .prefix, 470014910302⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 460784506798⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 457306855277⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 457306855277⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 454443907962⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 460784506798⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 455440188646⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 501410723977⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 452298310018⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 450472494217⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 475214118552⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 526647985960⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 451797055471⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 482527417355⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 454443907962⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 487415661807⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 461901979445⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 511921894062⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 493534555100⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 525700128683⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 478534703931⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 501440189719⟩,
    ⟨[0, 0, 0, 1], .prefix, 501410723977⟩,
    ⟨[0, 0, 0, 2], .prefix, 511818093666⟩,
    ⟨[0, 0, 0, 3], .prefix, 615539527004⟩,
    ⟨[0, 0, 1], .prefix, 526647985960⟩,
    ⟨[0, 0, 2], .prefix, 543030112802⟩,
    ⟨[0, 0, 3], .prefix, 561658269798⟩,
    ⟨[0, 0, 4], .prefix, 622823560537⟩,
    ⟨[0, 1], .prefix, 585597523172⟩,
    ⟨[0, 2], .prefix, 632767751741⟩,
    ⟨[0, 3], .prefix, 647962507149⟩,
    ⟨[0, 4], .prefix, 666590664145⟩,
    ⟨[0, 5], .prefix, 678929364174⟩,
    ⟨[0, 6], .prefix, 731431408240⟩,
    ⟨[0, 7], .prefix, 748492830279⟩,
    ⟨[1], .prefix, 659313059220⟩,
    ⟨[2], .prefix, 767816482622⟩,
    ⟨[3], .prefix, 821105604484⟩,
    ⟨[4], .prefix, 847000218252⟩,
    ⟨[5], .prefix, 859989793924⟩,
    ⟨[6], .prefix, 879056431396⟩,
    ⟨[7], .prefix, 904951045164⟩,
    ⟨[8], .prefix, 917940620836⟩,
    ⟨[9], .prefix, 1042895513135⟩,
    ⟨[10], .prefix, 1114571973959⟩,
    ⟨[11], .prefix, 1149540659273⟩,
    ⟨[12], .prefix, 1166602081312⟩,
    ⟨[13], .prefix, 1176706329520⟩,
    ⟨[14], .prefix, 1237871620259⟩,
    ⟨[15], .prefix, 1267641097323⟩,
    ⟨[16], .prefix, 1282316210418⟩,
    ⟨[17], .prefix, 1295822447171⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 103 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0

private theorem all_checked :
    certificates.all (checkResidueTerminal 103 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0,
    Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 103 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 103) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 103 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 103,
      hHat (residueBoxValue 103 v / 103) ≤ ((residueBoxValue 103 v / 103).divisors.card : ℚ) →
      hHat (residueBoxValue 103 v) < ((residueBoxValue 103 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP103
