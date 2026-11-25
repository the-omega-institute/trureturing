/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP61
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP61.residue_step
   digest: Complete residue-tree certificate for largest prime 61. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP61

def initialVector (r : ℕ) : ℕ :=
  if r < 61 then
    if r < 30 then
      if r < 15 then
        if r < 7 then
          if r < 3 then
            if r < 1 then
              0
            else
              if r < 2 then 259865578462 else 128894054336
          else
            if r < 5 then
              if r < 4 then 85258483306 else 63460659248
            else
              if r < 6 then 50400993263 else 41713012021
        else
          if r < 11 then
            if r < 9 then
              if r < 8 then 35525431027 else 30902672358
            else
              if r < 10 then 27325038523 else 24480782129
          else
            if r < 13 then
              if r < 12 then 22171593335 else 20265344555
            else
              if r < 14 then 18670645467 else 17322304761
      else
        if r < 22 then
          if r < 18 then
            if r < 16 then
              16172607871
            else
              if r < 17 then 15185866503 else 14334894177
          else
            if r < 20 then
              if r < 19 then 13598656446 else 12960666474
            else
              if r < 21 then 12407862148 else 11929807527
        else
          if r < 26 then
            if r < 24 then
              if r < 23 then 11518112793 else 11166009630
            else
              if r < 25 then 10868034146 else 10619791047
          else
            if r < 28 then
              if r < 27 then 10417774358 else 10259233833
            else
              if r < 29 then 10142074549 else 10064783645
    else
      if r < 45 then
        if r < 37 then
          if r < 33 then
            if r < 31 then
              10026379753
            else
              if r < 32 then 10026379753 else 10064783645
          else
            if r < 35 then
              if r < 34 then 10142074549 else 10259233833
            else
              if r < 36 then 10417774358 else 10619791047
        else
          if r < 41 then
            if r < 39 then
              if r < 38 then 10868034146 else 11166009630
            else
              if r < 40 then 11518112793 else 11929807527
          else
            if r < 43 then
              if r < 42 then 12407862148 else 12960666474
            else
              if r < 44 then 13598656446 else 14334894177
      else
        if r < 53 then
          if r < 49 then
            if r < 47 then
              if r < 46 then 15185866503 else 16172607871
            else
              if r < 48 then 17322304761 else 18670645467
          else
            if r < 51 then
              if r < 50 then 20265344555 else 22171593335
            else
              if r < 52 then 24480782129 else 27325038523
        else
          if r < 57 then
            if r < 55 then
              if r < 54 then 30902672358 else 35525431027
            else
              if r < 56 then 41713012021 else 50400993263
          else
            if r < 59 then
              if r < 58 then 63460659248 else 85258483306
            else
              if r < 60 then 128894054336 else 259865578462
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 290768250820⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 278536223929⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 274200472639⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 345124061768⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 270733612608⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], .kernel, 269891958215⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], .prefix, 658651591013⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], .prefix, 434848171659⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], .prefix, 417848052623⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], .prefix, 413353760808⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], .prefix, 515731128125⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], .prefix, 449302700610⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 271795385989⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 290768250820⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .prefix, 275051444965⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1], .prefix, 274200472639⟩,
    ⟨[0, 0, 0, 0, 0, 1], .prefix, 278536223929⟩,
    ⟨[0, 0, 0, 0, 0, 2], .prefix, 295858528690⟩,
    ⟨[0, 0, 0, 0, 1], .prefix, 282037171797⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 811208971724⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 613967328808⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 591173848720⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 634033197861⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 722561791420⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], .prefix, 647445382663⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], .prefix, 811208971724⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 0, 1], .prefix, 584433010780⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0, 1], .prefix, 613967328808⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 1], .prefix, 607799914292⟩,
    ⟨[0, 0, 0, 0, 2, 0, 1], .prefix, 634033197861⟩,
    ⟨[0, 0, 0, 0, 2, 1], .prefix, 591173848720⟩,
    ⟨[0, 0, 0, 0, 2, 2], .prefix, 635883241887⟩,
    ⟨[0, 0, 0, 1], .prefix, 295391009489⟩,
    ⟨[0, 0, 0, 2], .prefix, 320684346083⟩,
    ⟨[0, 0, 0, 3], .prefix, 356209777110⟩,
    ⟨[0, 0, 1], .prefix, 310266571725⟩,
    ⟨[0, 0, 2], .prefix, 330531916280⟩,
    ⟨[0, 0, 3], .prefix, 406144846078⟩,
    ⟨[0, 0, 4], .prefix, 426410190633⟩,
    ⟨[0, 1], .prefix, 345124061768⟩,
    ⟨[0, 2], .prefix, 372449100291⟩,
    ⟨[0, 3], .prefix, 384856962439⟩,
    ⟨[0, 4], .prefix, 395116196272⟩,
    ⟨[0, 5], .prefix, 654981774734⟩,
    ⟨[0, 6], .prefix, 740240258040⟩,
    ⟨[0, 7], .prefix, 767565296563⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 658651591013⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 434848171659⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 417848052623⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 413353760808⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 515731128125⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 449302700610⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 658651591013⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 484082899749⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1], .prefix, 434848171659⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .prefix, 414010282946⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .prefix, 413353760808⟩,
    ⟨[1, 0, 0, 0, 0, 1], .prefix, 417848052623⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 445312431933⟩,
    ⟨[1, 0, 0, 0, 1], .prefix, 422449338926⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 61 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 0, 2], .prefix, 811208971724⟩,
    ⟨[1, 0, 0, 1], .prefix, 441607368586⟩,
    ⟨[1, 0, 0, 2], .prefix, 501384221071⟩,
    ⟨[1, 0, 0, 3], .prefix, 554231956859⟩,
    ⟨[1, 0, 1], .prefix, 463641408190⟩,
    ⟨[1, 0, 2], .prefix, 496432792572⟩,
    ⟨[1, 0, 3], .prefix, 623404287899⟩,
    ⟨[1, 0, 4], .prefix, 654537666600⟩,
    ⟨[1, 1], .prefix, 515731128125⟩,
    ⟨[1, 2], .prefix, 556654823094⟩,
    ⟨[1, 3], .prefix, 602439487954⟩,
    ⟨[1, 4], .prefix, 626777157629⟩,
    ⟨[1, 5], .prefix, 1015536790427⟩,
    ⟨[1, 6], .prefix, 1142508285754⟩,
    ⟨[1, 7], .prefix, 1183431980723⟩,
    ⟨[2], .prefix, 452220292046⟩,
    ⟨[3], .prefix, 483122964404⟩,
    ⟨[4], .prefix, 498308830907⟩,
    ⟨[5], .prefix, 509321952028⟩,
    ⟨[6], .prefix, 593632097858⟩,
    ⟨[7], .prefix, 635345109879⟩,
    ⟨[8], .prefix, 655610454434⟩,
    ⟨[9], .prefix, 666478488580⟩,
    ⟨[10], .prefix, 685149134047⟩,
    ⟨[11], .prefix, 695566908405⟩,
    ⟨[12], .prefix, 722891946928⟩,
    ⟨[13], .prefix, 736490603374⟩,
    ⟨[14], .prefix, 749090934552⟩,
    ⟨[15], .prefix, 784890218674⟩,
    ⟨[16], .prefix, 805155563229⟩,
    ⟨[17], .prefix, 816023597375⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 61 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1

private theorem all_checked :
    certificates.all (checkResidueTerminal 61 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 61 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 61) =
      true := by decide +kernel

private theorem chunk_checked :
    checkResidueTree 61 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 61,
      hHat (residueBoxValue 61 v / 61) ≤ ((residueBoxValue 61 v / 61).divisors.card : ℚ) →
      hHat (residueBoxValue 61 v) < ((residueBoxValue 61 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP61
