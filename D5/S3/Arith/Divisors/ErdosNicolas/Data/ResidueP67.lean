/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP67
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP67.residue_step
   digest: Complete residue-tree certificate for largest prime 67. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP67

def initialVector (r : ℕ) : ℕ :=
  if r < 67 then
    if r < 33 then
      if r < 16 then
        if r < 8 then
          if r < 4 then
            if r < 2 then
              if r < 1 then 0 else 285633385789
            else
              if r < 3 then 141774119513 else 93839888284
          else
            if r < 6 then
              if r < 5 then 69890021451 else 55536420836
            else
              if r < 7 then 45983092640 else 39174653274
        else
          if r < 12 then
            if r < 10 then
              if r < 9 then 34083454326 else 30138626651
            else
              if r < 11 then 26997696667 else 24442777024
          else
            if r < 14 then
              if r < 13 then 22328662106 else 20554879986
            else
              if r < 15 then 19049722239 else 17760663076
      else
        if r < 24 then
          if r < 20 then
            if r < 18 then
              if r < 17 then 16648371420 else 15682837435
            else
              if r < 19 then 14840790078 else 14103932252
          else
            if r < 22 then
              if r < 21 then 13457705259 else 12890407884
            else
              if r < 23 then 12392555808 else 11956410866
        else
          if r < 28 then
            if r < 26 then
              if r < 25 then 11575627823 else 11244988451
            else
              if r < 27 then 10960197849 else 10717728802
          else
            if r < 30 then
              if r < 29 then 10514700712 else 10348786669
            else
              if r < 31 then
                10218142096
              else
                if r < 32 then 10121349742 else 10057379616
    else
      if r < 50 then
        if r < 41 then
          if r < 37 then
            if r < 35 then
              if r < 34 then 10025560177 else 10025560177
            else
              if r < 36 then 10057379616 else 10121349742
          else
            if r < 39 then
              if r < 38 then 10218142096 else 10348786669
            else
              if r < 40 then 10514700712 else 10717728802
        else
          if r < 45 then
            if r < 43 then
              if r < 42 then 10960197849 else 11244988451
            else
              if r < 44 then 11575627823 else 11956410866
          else
            if r < 47 then
              if r < 46 then 12392555808 else 12890407884
            else
              if r < 48 then
                13457705259
              else
                if r < 49 then 14103932252 else 14840790078
      else
        if r < 58 then
          if r < 54 then
            if r < 52 then
              if r < 51 then 15682837435 else 16648371420
            else
              if r < 53 then 17760663076 else 19049722239
          else
            if r < 56 then
              if r < 55 then 20554879986 else 22328662106
            else
              if r < 57 then 24442777024 else 26997696667
        else
          if r < 62 then
            if r < 60 then
              if r < 59 then 30138626651 else 34083454326
            else
              if r < 61 then 39174653274 else 45983092640
          else
            if r < 64 then
              if r < 63 then 55536420836 else 69890021451
            else
              if r < 65 then
                93839888284
              else
                if r < 66 then 141774119513 else 285633385789
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 331616478429⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 319716840115⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 304683108028⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 312631082456⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 304683108028⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 300474175867⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 295982172458⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 306188265775⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 295982172458⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 297589796655⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 324808039063⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 355523407240⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 306188265775⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 316309615517⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 331616478429⟩,
    ⟨[0, 0, 0, 0, 2], .prefix, 356059255453⟩,
    ⟨[0, 0, 0, 1], .prefix, 324808039063⟩,
    ⟨[0, 0, 0, 2], .prefix, 339648829141⟩,
    ⟨[0, 0, 0, 3], .prefix, 373732283467⟩,
    ⟨[0, 0, 1], .prefix, 341169806625⟩,
    ⟨[0, 0, 2], .prefix, 352414795076⟩,
    ⟨[0, 0, 3], .prefix, 385970989753⟩,
    ⟨[0, 0, 4], .prefix, 442035120277⟩,
    ⟨[0, 1], .prefix, 379473274073⟩,
    ⟨[0, 2], .prefix, 409611900724⟩,
    ⟨[0, 3], .prefix, 422004456532⟩,
    ⟨[0, 4], .prefix, 465162913793⟩,
    ⟨[0, 5], .prefix, 495301540444⟩,
    ⟨[0, 6], .prefix, 510821995942⟩,
    ⟨[0, 7], .prefix, 540960622593⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 495719260048⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 478139331048⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 456971928253⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 467862907228⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 456971928253⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 456128366227⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 476800300672⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 493065275880⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 476800300672⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 531304773202⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 485631880815⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 531380981079⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 493065275880⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 562819851037⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 495719260048⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 561377030626⟩,
    ⟨[1, 0, 0, 1], .prefix, 485631880815⟩,
    ⟨[1, 0, 0, 2], .prefix, 510594020635⟩,
    ⟨[1, 0, 0, 3], .prefix, 561325846381⟩,
    ⟨[1, 0, 1], .prefix, 509941622805⟩,
    ⟨[1, 0, 2], .prefix, 541214231593⟩,
    ⟨[1, 0, 3], .prefix, 591946057339⟩,
    ⟨[1, 0, 4], .prefix, 677213725932⟩,
    ⟨[1, 1], .prefix, 567230486226⟩,
    ⟨[1, 2], .prefix, 612209902955⟩,
    ⟨[1, 3], .prefix, 643482511743⟩,
    ⟨[1, 4], .prefix, 702092375575⟩,
    ⟨[1, 5], .prefix, 747071792304⟩,
    ⟨[1, 6], .prefix, 778503761396⟩,
    ⟨[1, 7], .prefix, 823483178125⟩,
    ⟨[2], .prefix, 497297526753⟩,
    ⟨[3], .prefix, 531380981079⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 67 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[4], .prefix, 548029352499⟩,
    ⟨[5], .prefix, 558086732115⟩,
    ⟨[6], .prefix, 651926620399⟩,
    ⟨[7], .prefix, 697909713039⟩,
    ⟨[8], .prefix, 720238375145⟩,
    ⟨[9], .prefix, 731814002968⟩,
    ⟨[10], .prefix, 745946772757⟩,
    ⟨[11], .prefix, 757522400580⟩,
    ⟨[12], .prefix, 786405348540⟩,
    ⟨[13], .prefix, 801246138618⟩,
    ⟨[14], .prefix, 812113746152⟩,
    ⟨[15], .prefix, 866903909196⟩,
    ⟨[16], .prefix, 893901605863⟩,
    ⟨[17], .prefix, 907359311122⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 67 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 67 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 67 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 67) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 67 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 67,
      hHat (residueBoxValue 67 v / 67) ≤ ((residueBoxValue 67 v / 67).divisors.card : ℚ) →
      hHat (residueBoxValue 67 v) < ((residueBoxValue 67 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP67
