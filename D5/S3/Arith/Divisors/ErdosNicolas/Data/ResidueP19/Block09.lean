/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block09
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block09.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block09

def certificates : List ResidueTerminal :=
  [
    ⟨[4, 0, 1, 0, 0, 0, 1], .kernel, 600149000463⟩,
    ⟨[4, 0, 1, 0, 0, 1], .prefix, 543660924151⟩,
    ⟨[4, 0, 1, 0, 0, 2], .prefix, 804272424373⟩,
    ⟨[4, 0, 1, 0, 1], .prefix, 565551370724⟩,
    ⟨[4, 0, 1, 0, 2], .prefix, 769186059629⟩,
    ⟨[4, 0, 1, 1], .prefix, 565551370724⟩,
    ⟨[4, 0, 1, 2], .prefix, 769186059629⟩,
    ⟨[4, 0, 1, 3], .prefix, 1083062849570⟩,
    ⟨[4, 0, 2, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[4, 0, 2, 0, 0, 0, 1], .prefix, 884010721493⟩,
    ⟨[4, 0, 2, 0, 0, 1], .prefix, 791727348200⟩,
    ⟨[4, 0, 2, 0, 0, 2], .prefix, 1194650861914⟩,
    ⟨[4, 0, 2, 0, 1], .prefix, 804272424373⟩,
    ⟨[4, 0, 2, 0, 2], .prefix, 1113043745390⟩,
    ⟨[4, 0, 2, 1], .prefix, 804272424373⟩,
    ⟨[4, 0, 2, 2], .prefix, 1113043745390⟩,
    ⟨[4, 0, 2, 3], .prefix, 1577713948487⟩,
    ⟨[4, 0, 3], .prefix, 543660924151⟩,
    ⟨[4, 0, 4], .prefix, 646410911182⟩,
    ⟨[4, 1], .prefix, 302147545116⟩,
    ⟨[4, 2], .prefix, 408664261627⟩,
    ⟨[4, 3], .prefix, 563626550321⟩,
    ⟨[4, 4], .prefix, 643674586795⟩,
    ⟨[4, 5], .prefix, 805139929356⟩,
    ⟨[4, 6], .prefix, 880363920930⟩,
    ⟨[4, 7], .prefix, 1038225434121⟩,
    ⟨[5, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[5, 0, 0, 0, 0, 0, 1], .prefix, 369374700711⟩,
    ⟨[5, 0, 0, 0, 0, 1], .prefix, 353825201012⟩,
    ⟨[5, 0, 0, 0, 0, 2], .prefix, 523731808018⟩,
    ⟨[5, 0, 0, 0, 1], .prefix, 359922431200⟩,
    ⟨[5, 0, 0, 0, 2], .prefix, 445217498156⟩,
    ⟨[5, 0, 0, 1], .prefix, 359922431200⟩,
    ⟨[5, 0, 0, 2], .prefix, 445217498156⟩,
    ⟨[5, 0, 0, 3], .prefix, 631273010705⟩,
    ⟨[5, 0, 1], .prefix, 359054926217⟩,
    ⟨[5, 0, 2], .prefix, 526824614680⟩,
    ⟨[5, 0, 3], .prefix, 629404191301⟩,
    ⟨[5, 0, 4], .prefix, 791727348200⟩,
    ⟨[5, 1], .prefix, 353825201012⟩,
    ⟨[5, 2], .prefix, 523731808018⟩,
    ⟨[5, 3], .prefix, 691501496481⟩,
    ⟨[5, 4], .prefix, 809362473662⟩,
    ⟨[5, 5], .prefix, 983229392313⟩,
    ⟨[5, 6], .prefix, 1077358013844⟩,
    ⟨[5, 7], .prefix, 1250357427512⟩,
    ⟨[6], .prefix, 198457088639⟩,
    ⟨[7], .prefix, 212537673696⟩,
    ⟨[8], .prefix, 222608749078⟩,
    ⟨[9], .prefix, 302147545116⟩,
    ⟨[10, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[10, 0, 0, 0, 0, 0, 1], .prefix, 653236421741⟩,
    ⟨[10, 0, 0, 0, 0, 1], .prefix, 601891625061⟩,
    ⟨[10, 0, 0, 0, 0, 2], .prefix, 914110245559⟩,
    ⟨[10, 0, 0, 0, 1], .prefix, 599560980979⟩,
    ⟨[10, 0, 0, 0, 2], .prefix, 848651891204⟩,
    ⟨[10, 0, 0, 1], .prefix, 599560980979⟩,
    ⟨[10, 0, 0, 2], .prefix, 848651891204⟩,
    ⟨[10, 0, 0, 3], .prefix, 1189669692447⟩,
    ⟨[10, 0, 1], .prefix, 593007935965⟩,
    ⟨[10, 0, 2], .prefix, 853881759783⟩,
    ⟨[10, 0, 3], .prefix, 1102972670008⟩,
    ⟨[10, 0, 4], .prefix, 1415191290506⟩,
    ⟨[10, 1], .prefix, 601891625061⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block09
