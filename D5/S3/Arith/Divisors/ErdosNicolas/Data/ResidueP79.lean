/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP79
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP79.residue_step
   digest: Complete residue-tree certificate for largest prime 79. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP79

def initialVector (r : ℕ) : ℕ :=
  if r < 79 then
    if r < 39 then
      if r < 19 then
        if r < 9 then
          if r < 4 then
            if r < 2 then
              if r < 1 then 0 else 330767545532
            else
              if r < 3 then 161172831267 else 104680409138
          else
            if r < 6 then
              if r < 5 then 76464734457 else 59560749273
            else
              if r < 7 then
                48313479220
              else
                if r < 8 then 40299405511 else 34306807502
        else
          if r < 14 then
            if r < 11 then
              if r < 10 then 29662544047 else 25962766119
            else
              if r < 12 then
                22950513815
              else
                if r < 13 then 20454514740 else 18356229789
          else
            if r < 16 then
              if r < 15 then 16571022233 else 15036859534
            else
              if r < 17 then
                13707251851
              else
                if r < 18 then 12546683549 else 11527567117
      else
        if r < 29 then
          if r < 24 then
            if r < 21 then
              if r < 20 then 10628160412 else 9831107371
            else
              if r < 22 then
                9122397818
              else
                if r < 23 then 8490609301 else 7926348878
          else
            if r < 26 then
              if r < 25 then 7421833706 else 6970572908
            else
              if r < 27 then
                6567123463
              else
                if r < 28 then 6206900764 else 5886030256
        else
          if r < 34 then
            if r < 31 then
              if r < 30 then 5601229805 else 5349717821
            else
              if r < 32 then
                5129137813
              else
                if r < 33 then 4937498981 else 4773129132
          else
            if r < 36 then
              if r < 35 then 4634634706 else 4520871546
            else
              if r < 37 then
                4430919223
              else
                if r < 38 then 4364062787 else 4319777836
    else
      if r < 59 then
        if r < 49 then
          if r < 44 then
            if r < 41 then
              if r < 40 then 4297720562 else 4297720562
            else
              if r < 42 then
                4319777836
              else
                if r < 43 then 4364062787 else 4430919223
          else
            if r < 46 then
              if r < 45 then 4520871546 else 4634634706
            else
              if r < 47 then
                4773129132
              else
                if r < 48 then 4937498981 else 5129137813
        else
          if r < 54 then
            if r < 51 then
              if r < 50 then 5349717821 else 5601229805
            else
              if r < 52 then
                5886030256
              else
                if r < 53 then 6206900764 else 6567123463
          else
            if r < 56 then
              if r < 55 then 6970572908 else 7421833706
            else
              if r < 57 then
                7926348878
              else
                if r < 58 then 8490609301 else 9122397818
      else
        if r < 69 then
          if r < 64 then
            if r < 61 then
              if r < 60 then 9831107371 else 10628160412
            else
              if r < 62 then
                11527567117
              else
                if r < 63 then 12546683549 else 13707251851
          else
            if r < 66 then
              if r < 65 then 15036859534 else 16571022233
            else
              if r < 67 then
                18356229789
              else
                if r < 68 then 20454514740 else 22950513815
        else
          if r < 74 then
            if r < 71 then
              if r < 70 then 25962766119 else 29662544047
            else
              if r < 72 then
                34306807502
              else
                if r < 73 then 40299405511 else 48313479220
          else
            if r < 76 then
              if r < 75 then 59560749273 else 76464734457
            else
              if r < 77 then
                104680409138
              else
                if r < 78 then 161172831267 else 330767545532
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 379081024752⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 365074353034⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 351222060272⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 342295112649⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 407232279989⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 435447954670⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 335705044513⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 353718059347⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 336974446296⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 335705044513⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 336653575788⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 336368775337⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 338693894410⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 341395705944⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 347338567765⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 379081024752⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 397437254541⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 353718059347⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 358148978570⟩,
    ⟨[0, 0, 0, 1], .prefix, 371066951043⟩,
    ⟨[0, 0, 0, 2], .prefix, 376416668864⟩,
    ⟨[0, 0, 0, 3], .prefix, 382623569628⟩,
    ⟨[0, 0, 1], .prefix, 390328294805⟩,
    ⟨[0, 0, 2], .prefix, 404035546656⟩,
    ⟨[0, 0, 3], .prefix, 414663707068⟩,
    ⟨[0, 0, 4], .prefix, 442371402356⟩,
    ⟨[0, 1], .prefix, 435447954670⟩,
    ⟨[0, 2], .prefix, 465110498717⟩,
    ⟨[0, 3], .prefix, 471677622180⟩,
    ⟨[0, 4], .prefix, 632490230748⟩,
    ⟨[0, 5], .prefix, 680803709968⟩,
    ⟨[0, 6], .prefix, 692331277085⟩,
    ⟨[0, 7], .prefix, 699301849993⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 560708370759⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 539954436152⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 519816725245⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 507898863139⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 602711918758⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 644934265157⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 555865188859⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 536670701533⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 600940563773⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 555865188859⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 509616198161⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 507918255032⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 504639854809⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 506888315047⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 514397429288⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 560708370759⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 605438695493⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 536670701533⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 587306311975⟩,
    ⟨[1, 0, 0, 1], .prefix, 548810804543⟩,
    ⟨[1, 0, 0, 2], .prefix, 576395953064⟩,
    ⟨[1, 0, 0, 3], .prefix, 643249339917⟩,
    ⟨[1, 0, 1], .prefix, 577463892191⟩,
    ⟨[1, 0, 2], .prefix, 596108643023⟩,
    ⟨[1, 0, 3], .prefix, 613165053825⟩,
    ⟨[1, 0, 4], .prefix, 670035481569⟩,
    ⟨[1, 1], .prefix, 644934265157⟩,
    ⟨[1, 2], .prefix, 686124376321⟩,
    ⟨[1, 3], .prefix, 699301849993⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 79 1 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 4], .prefix, 982963269687⟩,
    ⟨[1, 5], .prefix, 1135957158045⟩,
    ⟨[1, 6], .prefix, 1177147269209⟩,
    ⟨[1, 7], .prefix, 1202070622461⟩,
    ⟨[2], .prefix, 568405111256⟩,
    ⟨[3], .prefix, 602711918758⟩,
    ⟨[4], .prefix, 616419170609⟩,
    ⟨[5], .prefix, 621356669590⟩,
    ⟨[6], .prefix, 668057454581⟩,
    ⟨[7], .prefix, 702364262083⟩,
    ⟨[8], .prefix, 716071513934⟩,
    ⟨[9], .prefix, 721009012915⟩,
    ⟨[10], .prefix, 761371594331⟩,
    ⟨[11], .prefix, 809685073551⟩,
    ⟨[12], .prefix, 830139588291⟩,
    ⟨[13], .prefix, 837561421997⟩,
    ⟨[14], .prefix, 861023937656⟩,
    ⟨[15], .prefix, 909337416876⟩,
    ⟨[16], .prefix, 929791931616⟩,
    ⟨[17], .prefix, 937213765322⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 79 1 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 79 1 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 79 1 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 79) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 79 1 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 79,
      hHat (residueBoxValue 79 v / 79) ≤ ((residueBoxValue 79 v / 79).divisors.card : ℚ) →
      hHat (residueBoxValue 79 v) < ((residueBoxValue 79 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP79
