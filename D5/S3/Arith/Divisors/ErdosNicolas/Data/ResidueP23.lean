/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP23
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP23.chunk_checked,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP23.residue_step
   digest: Complete residue-tree certificate for largest prime 23. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The checker verifies every terminal and complete coverage of the exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP23

def initialVector (r : ℕ) : ℕ :=
  if r < 23 then
    if r < 11 then
      if r < 5 then
        if r < 2 then
          if r < 1 then 0 else 96700754868
        else
          if r < 3 then
            47407700313
          else
            if r < 4 then 31079095378 else 23021012787
      else
        if r < 8 then
          if r < 6 then
            18297342247
          else
            if r < 7 then 15265937141 else 13226886723
        else
          if r < 9 then
            11834919777
          else
            if r < 10 then 10903995674 else 10329780181
    else
      if r < 17 then
        if r < 14 then
          if r < 12 then
            10055331117
          else
            if r < 13 then 10055331117 else 10329780181
        else
          if r < 15 then
            10903995674
          else
            if r < 16 then 11834919777 else 13226886723
      else
        if r < 20 then
          if r < 18 then
            15265937141
          else
            if r < 19 then 18297342247 else 23021012787
        else
          if r < 21 then
            31079095378
          else
            if r < 22 then 47407700313 else 96700754868
  else 0

private def block0 : List ResidueTerminal :=
  [
    ⟨[0, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 0, 1, 0, 1], .prefix, 151245996625⟩,
    ⟨[0, 0, 0, 0, 0, 1, 1], .prefix, 151245996625⟩,
    ⟨[0, 0, 0, 0, 0, 2, 0, 0], .kernel, 118865454826⟩,
    ⟨[0, 0, 0, 0, 0, 2, 0, 1], .prefix, 197591029144⟩,
    ⟨[0, 0, 0, 0, 0, 2, 1], .prefix, 197591029144⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1, 0], .kernel, 153101118504⟩,
    ⟨[0, 0, 0, 0, 1, 0, 1, 1], .kernel, 330285917589⟩,
    ⟨[0, 0, 0, 0, 1, 1, 0, 0], .kernel, 135383208413⟩,
    ⟨[0, 0, 0, 0, 1, 1, 0, 1], .prefix, 252156954032⟩,
    ⟨[0, 0, 0, 0, 1, 1, 1], .prefix, 252156954032⟩,
    ⟨[0, 0, 0, 0, 1, 2], .prefix, 214584370097⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 0], .kernel, 122022023126⟩,
    ⟨[0, 0, 0, 0, 2, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 0, 0, 0, 2, 0, 1, 0], .kernel, 178696835826⟩,
    ⟨[0, 0, 0, 0, 2, 0, 1, 1], .prefix, 504363778349⟩,
    ⟨[0, 0, 0, 0, 2, 1], .prefix, 223804280668⟩,
    ⟨[0, 0, 0, 0, 2, 2], .prefix, 266232505312⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 0, 0, 0, 1], .prefix, 151245996625⟩,
    ⟨[0, 0, 0, 1, 0, 0, 1], .prefix, 151245996625⟩,
    ⟨[0, 0, 0, 1, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 1, 0, 1, 0, 1], .prefix, 296563481602⟩,
    ⟨[0, 0, 0, 1, 0, 1, 1], .prefix, 296563481602⟩,
    ⟨[0, 0, 0, 1, 0, 2, 0, 0], .kernel, 239122876598⟩,
    ⟨[0, 0, 0, 1, 0, 2, 0, 1], .prefix, 369222137067⟩,
    ⟨[0, 0, 0, 1, 0, 2, 1], .prefix, 369222137067⟩,
    ⟨[0, 0, 0, 1, 1, 0, 0, 0], .kernel, 131817892485⟩,
    ⟨[0, 0, 0, 1, 1, 0, 0, 1], .prefix, 252156954032⟩,
    ⟨[0, 0, 0, 1, 1, 0, 1], .prefix, 252156954032⟩,
    ⟨[0, 0, 0, 1, 1, 1, 0, 0], .kernel, 267201100898⟩,
    ⟨[0, 0, 0, 1, 1, 1, 0, 1], .prefix, 483604897538⟩,
    ⟨[0, 0, 0, 1, 1, 1, 1], .prefix, 483604897538⟩,
    ⟨[0, 0, 0, 1, 1, 2], .prefix, 424232583234⟩,
    ⟨[0, 0, 0, 1, 2], .prefix, 223804280668⟩,
    ⟨[0, 0, 0, 2, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 2, 0, 0, 0, 1], .prefix, 197591029144⟩,
    ⟨[0, 0, 0, 2, 0, 0, 1], .prefix, 197591029144⟩,
    ⟨[0, 0, 0, 2, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 2, 0, 1, 0, 1], .prefix, 369222137067⟩,
    ⟨[0, 0, 0, 2, 0, 1, 1], .prefix, 369222137067⟩,
    ⟨[0, 0, 0, 2, 0, 2], .prefix, 380129613567⟩,
    ⟨[0, 0, 0, 2, 1], .prefix, 214584370097⟩,
    ⟨[0, 0, 0, 2, 2], .prefix, 266232505312⟩,
    ⟨[0, 0, 0, 3, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 0, 3, 0, 0, 0, 1], .prefix, 255054060574⟩,
    ⟨[0, 0, 0, 3, 0, 0, 1], .prefix, 255054060574⟩,
    ⟨[0, 0, 0, 3, 0, 1], .prefix, 339750954432⟩,
    ⟨[0, 0, 0, 3, 0, 2], .prefix, 471843295981⟩,
    ⟨[0, 0, 0, 3, 1], .prefix, 317335223225⟩,
    ⟨[0, 0, 0, 3, 2], .prefix, 413933869140⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 0, 0, 0, 0, 1], .prefix, 169098205280⟩,
    ⟨[0, 0, 1, 0, 0, 0, 1], .prefix, 169098205280⟩,
    ⟨[0, 0, 1, 0, 0, 1], .prefix, 165342231036⟩,
    ⟨[0, 0, 1, 0, 0, 2], .prefix, 208256246191⟩,
    ⟨[0, 0, 1, 0, 1], .prefix, 173309793102⟩,
    ⟨[0, 0, 1, 0, 2], .prefix, 226835685774⟩
  ]

private theorem checked0 :
    block0.all (checkResidueTerminal 23 2 4294967296 initialVector) = true := by
  decide +kernel

private def block1 : List ResidueTerminal :=
  [
    ⟨[0, 0, 1, 1], .prefix, 165342231036⟩,
    ⟨[0, 0, 1, 2], .prefix, 208256246191⟩,
    ⟨[0, 0, 1, 3], .prefix, 255902725131⟩,
    ⟨[0, 0, 2, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 2, 0, 0, 0, 0, 1], .prefix, 228340825370⟩,
    ⟨[0, 0, 2, 0, 0, 0, 1], .prefix, 228340825370⟩,
    ⟨[0, 0, 2, 0, 0, 1], .prefix, 226835685774⟩,
    ⟨[0, 0, 2, 0, 0, 2], .prefix, 267163429415⟩,
    ⟨[0, 0, 2, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 2, 0, 1, 0, 0, 1], .prefix, 426759400310⟩,
    ⟨[0, 0, 2, 0, 1, 0, 1], .prefix, 426759400310⟩,
    ⟨[0, 0, 2, 0, 1, 1], .prefix, 420530590174⟩,
    ⟨[0, 0, 2, 0, 1, 2], .prefix, 526793361757⟩,
    ⟨[0, 0, 2, 0, 2], .prefix, 360824372368⟩,
    ⟨[0, 0, 2, 1], .prefix, 226835685774⟩,
    ⟨[0, 0, 2, 2], .prefix, 267163429415⟩,
    ⟨[0, 0, 2, 3], .prefix, 384823511074⟩,
    ⟨[0, 0, 3], .prefix, 173309793102⟩,
    ⟨[0, 0, 4], .prefix, 195756590396⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0, 1], .prefix, 171209312099⟩,
    ⟨[0, 1, 0, 0, 0, 0, 1], .prefix, 171209312099⟩,
    ⟨[0, 1, 0, 0, 0, 1, 0, 0], .kernel, 151336517150⟩,
    ⟨[0, 1, 0, 0, 0, 1, 0, 1], .prefix, 255054060574⟩,
    ⟨[0, 1, 0, 0, 0, 1, 1], .prefix, 255054060574⟩,
    ⟨[0, 1, 0, 0, 0, 2], .prefix, 259872191795⟩,
    ⟨[0, 1, 0, 0, 1, 0, 0, 0], .kernel, 148164961544⟩,
    ⟨[0, 1, 0, 0, 1, 0, 0, 1], .prefix, 332065506249⟩,
    ⟨[0, 1, 0, 0, 1, 0, 1], .prefix, 332065506249⟩,
    ⟨[0, 1, 0, 0, 1, 1], .prefix, 317335223225⟩,
    ⟨[0, 1, 0, 0, 1, 2], .prefix, 425163507337⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 223529831604⟩,
    ⟨[0, 1, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 1, 0, 0, 0, 1], .prefix, 255054060574⟩,
    ⟨[0, 1, 0, 1, 0, 0, 1], .prefix, 255054060574⟩,
    ⟨[0, 1, 0, 1, 0, 1], .prefix, 339750954432⟩,
    ⟨[0, 1, 0, 1, 0, 2], .prefix, 471843295981⟩,
    ⟨[0, 1, 0, 1, 1], .prefix, 317335223225⟩,
    ⟨[0, 1, 0, 1, 2], .prefix, 413933869140⟩,
    ⟨[0, 1, 0, 2], .prefix, 259872191795⟩,
    ⟨[0, 1, 0, 3], .prefix, 320506778831⟩,
    ⟨[0, 1, 1], .prefix, 161704858707⟩,
    ⟨[0, 1, 2], .prefix, 220585749724⟩,
    ⟨[0, 1, 3], .prefix, 254510758185⟩,
    ⟨[0, 1, 4], .prefix, 278067425089⟩,
    ⟨[0, 2, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 0, 0, 0, 1], .prefix, 220585749724⟩,
    ⟨[0, 2, 0, 0, 0, 0, 1], .prefix, 220585749724⟩,
    ⟨[0, 2, 0, 0, 0, 1], .prefix, 214584370097⟩,
    ⟨[0, 2, 0, 0, 0, 2], .prefix, 349262983160⟩,
    ⟨[0, 2, 0, 0, 1], .prefix, 219654825621⟩,
    ⟨[0, 2, 0, 0, 2], .prefix, 263991873809⟩,
    ⟨[0, 2, 0, 1], .prefix, 214584370097⟩,
    ⟨[0, 2, 0, 2], .prefix, 349262983160⟩,
    ⟨[0, 2, 0, 3], .prefix, 425163507337⟩,
    ⟨[0, 2, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 2, 1, 0, 0, 0, 0, 1], .prefix, 412422870455⟩,
    ⟨[0, 2, 1, 0, 0, 0, 1], .prefix, 412422870455⟩,
    ⟨[0, 2, 1, 0, 0, 1], .prefix, 379887354114⟩,
    ⟨[0, 2, 1, 0, 0, 2], .prefix, 579648258872⟩,
    ⟨[0, 2, 1, 0, 1], .prefix, 417452209730⟩,
    ⟨[0, 2, 1, 0, 2], .prefix, 526793361757⟩,
    ⟨[0, 2, 1, 1], .prefix, 379887354114⟩,
    ⟨[0, 2, 1, 2], .prefix, 579648258872⟩
  ]

private theorem checked1 :
    block1.all (checkResidueTerminal 23 2 4294967296 initialVector) = true := by
  decide +kernel

private def block2 : List ResidueTerminal :=
  [
    ⟨[0, 2, 1, 3], .prefix, 731583605790⟩,
    ⟨[0, 2, 2], .prefix, 346487842513⟩,
    ⟨[0, 2, 3], .prefix, 417452209730⟩,
    ⟨[0, 2, 4], .prefix, 461432549308⟩,
    ⟨[0, 3], .prefix, 161704858707⟩,
    ⟨[0, 4], .prefix, 189506654346⟩,
    ⟨[0, 5], .prefix, 220585749724⟩,
    ⟨[0, 6], .prefix, 233812636447⟩,
    ⟨[0, 7], .prefix, 254510758185⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1, 0], .kernel, 169429723439⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 1, 0, 1], .prefix, 252156954032⟩,
    ⟨[1, 0, 0, 0, 0, 1, 1], .prefix, 252156954032⟩,
    ⟨[1, 0, 0, 0, 0, 2], .prefix, 214584370097⟩,
    ⟨[1, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 1, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 1, 0, 1, 0], .kernel, 322530841943⟩,
    ⟨[1, 0, 0, 0, 1, 0, 1, 1], .prefix, 678680028773⟩,
    ⟨[1, 0, 0, 0, 1, 1], .prefix, 320900539153⟩,
    ⟨[1, 0, 0, 0, 1, 2], .prefix, 387811138141⟩,
    ⟨[1, 0, 0, 0, 2, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 2, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 2, 0, 1, 0], .kernel, 389260985760⟩,
    ⟨[1, 0, 0, 0, 2, 0, 1, 1], .prefix, 951355347458⟩,
    ⟨[1, 0, 0, 0, 2, 1], .prefix, 437674284772⟩,
    ⟨[1, 0, 0, 0, 2, 2], .prefix, 521722906233⟩,
    ⟨[1, 0, 0, 1, 0, 0, 0, 0], .kernel, 168239337578⟩,
    ⟨[1, 0, 0, 1, 0, 0, 0, 1], .prefix, 252156954032⟩,
    ⟨[1, 0, 0, 1, 0, 0, 1], .prefix, 252156954032⟩,
    ⟨[1, 0, 0, 1, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 1, 0, 1, 0, 1], .prefix, 483604897538⟩,
    ⟨[1, 0, 0, 1, 0, 1, 1], .prefix, 483604897538⟩,
    ⟨[1, 0, 0, 1, 0, 2], .prefix, 424232583234⟩,
    ⟨[1, 0, 0, 1, 1], .prefix, 320900539153⟩,
    ⟨[1, 0, 0, 1, 2], .prefix, 437674284772⟩,
    ⟨[1, 0, 0, 2], .prefix, 214584370097⟩,
    ⟨[1, 0, 0, 3], .prefix, 317335223225⟩,
    ⟨[1, 0, 1], .prefix, 173309793102⟩,
    ⟨[1, 0, 2, 0, 0, 0, 0, 0], .kernel, 243164290709⟩,
    ⟨[1, 0, 2, 0, 0, 0, 0, 1], .prefix, 426759400310⟩,
    ⟨[1, 0, 2, 0, 0, 0, 1], .prefix, 426759400310⟩,
    ⟨[1, 0, 2, 0, 0, 1], .prefix, 420530590174⟩,
    ⟨[1, 0, 2, 0, 0, 2], .prefix, 526793361757⟩,
    ⟨[1, 0, 2, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 2, 0, 1, 0, 0, 1], .prefix, 826131927659⟩,
    ⟨[1, 0, 2, 0, 1, 0, 1], .prefix, 826131927659⟩,
    ⟨[1, 0, 2, 0, 1, 1], .prefix, 786304721525⟩,
    ⟨[1, 0, 2, 0, 1, 2], .prefix, 1031632035150⟩,
    ⟨[1, 0, 2, 0, 2], .prefix, 679438406436⟩,
    ⟨[1, 0, 2, 1], .prefix, 420530590174⟩,
    ⟨[1, 0, 2, 2], .prefix, 526793361757⟩,
    ⟨[1, 0, 2, 3], .prefix, 720353967593⟩,
    ⟨[1, 0, 3], .prefix, 308693001515⟩,
    ⟨[1, 0, 4], .prefix, 379121714615⟩,
    ⟨[1, 1, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 1, 0, 0, 0, 0, 0, 1], .prefix, 332065506249⟩,
    ⟨[1, 1, 0, 0, 0, 0, 1], .prefix, 332065506249⟩,
    ⟨[1, 1, 0, 0, 0, 1], .prefix, 317335223225⟩,
    ⟨[1, 1, 0, 0, 0, 2], .prefix, 425163507337⟩,
    ⟨[1, 1, 0, 0, 1], .prefix, 338618449244⟩,
    ⟨[1, 1, 0, 0, 2], .prefix, 434368430602⟩
  ]

private theorem checked2 :
    block2.all (checkResidueTerminal 23 2 4294967296 initialVector) = true := by
  decide +kernel

private def block3 : List ResidueTerminal :=
  [
    ⟨[1, 1, 0, 1], .prefix, 317335223225⟩,
    ⟨[1, 1, 0, 2], .prefix, 425163507337⟩,
    ⟨[1, 1, 0, 3], .prefix, 573328468881⟩,
    ⟨[1, 1, 1], .prefix, 254510758185⟩,
    ⟨[1, 1, 2], .prefix, 402675719729⟩,
    ⟨[1, 1, 3], .prefix, 497235315226⟩,
    ⟨[1, 1, 4], .prefix, 552114630015⟩,
    ⟨[1, 2], .prefix, 219654825621⟩,
    ⟨[1, 3], .prefix, 254510758185⟩,
    ⟨[1, 4], .prefix, 361266844170⟩,
    ⟨[1, 5], .prefix, 402675719729⟩,
    ⟨[1, 6], .prefix, 427737526229⟩,
    ⟨[1, 7], .prefix, 497235315226⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0, 1], .kernel, 215212287255⟩,
    ⟨[2, 0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 0, 1, 1], .prefix, 504363778349⟩,
    ⟨[2, 0, 0, 0, 0, 1], .prefix, 223804280668⟩,
    ⟨[2, 0, 0, 0, 0, 2], .prefix, 266232505312⟩,
    ⟨[2, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 1, 0, 0, 1], .kernel, 451639706430⟩,
    ⟨[2, 0, 0, 0, 1, 0, 1, 0], .kernel, 499715641028⟩,
    ⟨[2, 0, 0, 0, 1, 0, 1, 1], .prefix, 951355347458⟩,
    ⟨[2, 0, 0, 0, 1, 1], .prefix, 437674284772⟩,
    ⟨[2, 0, 0, 0, 1, 2], .prefix, 521722906233⟩,
    ⟨[2, 0, 0, 0, 2, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 2, 0, 0, 1], .prefix, 740791197524⟩,
    ⟨[2, 0, 0, 0, 2, 0, 1], .prefix, 740791197524⟩,
    ⟨[2, 0, 0, 0, 2, 1], .prefix, 599227426000⟩,
    ⟨[2, 0, 0, 0, 2, 2], .prefix, 771727653744⟩,
    ⟨[2, 0, 0, 1], .prefix, 223804280668⟩,
    ⟨[2, 0, 0, 2], .prefix, 266232505312⟩,
    ⟨[2, 0, 0, 3], .prefix, 413933869140⟩,
    ⟨[2, 0, 1], .prefix, 226835685774⟩,
    ⟨[2, 0, 2], .prefix, 360824372368⟩,
    ⟨[2, 0, 3], .prefix, 420530590174⟩,
    ⟨[2, 0, 4], .prefix, 525274620138⟩,
    ⟨[2, 1], .prefix, 223529831604⟩,
    ⟨[2, 2], .prefix, 263991873809⟩,
    ⟨[2, 3], .prefix, 384823511074⟩,
    ⟨[2, 4], .prefix, 467087143951⟩,
    ⟨[2, 5], .prefix, 523487507587⟩,
    ⟨[2, 6], .prefix, 566190181295⟩,
    ⟨[2, 7], .prefix, 720353967593⟩,
    ⟨[3, 0, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[3, 0, 0, 0, 0, 0, 0, 1], .kernel, 237951202706⟩,
    ⟨[3, 0, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[3, 0, 0, 0, 0, 0, 1, 1], .prefix, 602961236274⟩,
    ⟨[3, 0, 0, 0, 0, 1], .prefix, 252156954032⟩,
    ⟨[3, 0, 0, 0, 0, 2], .prefix, 384823511074⟩,
    ⟨[3, 0, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[3, 0, 0, 0, 1, 0, 0, 1], .prefix, 678680028773⟩,
    ⟨[3, 0, 0, 0, 1, 0, 1], .prefix, 678680028773⟩,
    ⟨[3, 0, 0, 0, 1, 1], .prefix, 497851485594⟩,
    ⟨[3, 0, 0, 0, 1, 2], .prefix, 720353967593⟩,
    ⟨[3, 0, 0, 0, 2, 0, 0, 0], .direct, 0⟩,
    ⟨[3, 0, 0, 0, 2, 0, 0, 1], .prefix, 951355347458⟩,
    ⟨[3, 0, 0, 0, 2, 0, 1], .prefix, 951355347458⟩,
    ⟨[3, 0, 0, 0, 2, 1], .prefix, 746443123698⟩,
    ⟨[3, 0, 0, 0, 2, 2], .prefix, 1031497736586⟩,
    ⟨[3, 0, 0, 1], .prefix, 252156954032⟩,
    ⟨[3, 0, 0, 2], .prefix, 384823511074⟩,
    ⟨[3, 0, 0, 3], .prefix, 488631575023⟩,
    ⟨[3, 0, 1], .prefix, 253936542692⟩
  ]

private theorem checked3 :
    block3.all (checkResidueTerminal 23 2 4294967296 initialVector) = true := by
  decide +kernel

private def block4 : List ResidueTerminal :=
  [
    ⟨[3, 0, 2], .prefix, 426759400310⟩,
    ⟨[3, 0, 3], .prefix, 501731555257⟩,
    ⟨[3, 0, 4], .prefix, 648947128574⟩,
    ⟨[3, 1], .prefix, 332065506249⟩,
    ⟨[3, 2], .prefix, 402675719729⟩,
    ⟨[3, 3], .prefix, 477629410552⟩,
    ⟨[3, 4], .prefix, 638847333775⟩,
    ⟨[3, 5], .prefix, 726221048656⟩,
    ⟨[3, 6], .prefix, 796831262136⟩,
    ⟨[3, 7], .prefix, 937512356582⟩,
    ⟨[4], .prefix, 200508818817⟩,
    ⟨[5], .prefix, 223529831604⟩,
    ⟨[6], .prefix, 235364751381⟩,
    ⟨[7], .prefix, 252156954032⟩,
    ⟨[8], .prefix, 263991873809⟩,
    ⟨[9], .prefix, 278067425089⟩,
    ⟨[10], .prefix, 288122756206⟩,
    ⟨[11], .prefix, 384823511074⟩,
    ⟨[12], .prefix, 432231211387⟩,
    ⟨[13], .prefix, 455252224174⟩,
    ⟨[14], .prefix, 467087143951⟩,
    ⟨[15], .prefix, 488631575023⟩,
    ⟨[16], .prefix, 511652587810⟩,
    ⟨[17], .prefix, 523487507587⟩
  ]

private theorem checked4 :
    block4.all (checkResidueTerminal 23 2 4294967296 initialVector) = true := by
  decide +kernel

def certificates : List ResidueTerminal :=
  block0 ++ block1 ++ block2 ++ block3 ++ block4

private theorem all_checked :
    certificates.all (checkResidueTerminal 23 2 4294967296 initialVector) = true := by
  simp only [certificates, List.all_append, checked0, checked1, checked2, checked3, checked4,
    Bool.and_self]

private theorem initial_checked :
    checkResidueInitial 23 2 4294967296 initialVector = true := by decide +kernel

private theorem coverage_checked :
    checkPrefixCover (certificates.map ResidueTerminal.exponents) [] (residueCaps 23) =
      true := by decide +kernel

theorem chunk_checked :
    checkResidueTree 23 2 4294967296 initialVector certificates = true := by
  simp only [checkResidueTree, initial_checked, coverage_checked, all_checked, Bool.and_self]
  decide +kernel

theorem residue_step :
    ∀ v ∈ residueBox 23,
      hHat (residueBoxValue 23 v / 23) ≤ ((residueBoxValue 23 v / 23).divisors.card : ℚ) →
      hHat (residueBoxValue 23 v) < ((residueBoxValue 23 v).divisors.card : ℚ) :=
  checkResidueTree_sound chunk_checked

#print axioms chunk_checked
#print axioms residue_step

end D5.S3.Arith.ErdosNicolas.Data.ResidueP23
