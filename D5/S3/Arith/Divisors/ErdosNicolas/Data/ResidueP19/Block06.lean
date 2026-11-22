/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block06
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block06.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block06

def certificates : List ResidueTerminal :=
  [
    ⟨[1, 2, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 2, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 2, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[1, 2, 0, 0, 0, 1, 1], .kernel, 735854092027⟩,
    ⟨[1, 2, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[1, 2, 0, 0, 0, 2, 1], .kernel, 1049828123590⟩,
    ⟨[1, 2, 0, 0, 1], .prefix, 364144975506⟩,
    ⟨[1, 2, 0, 0, 2], .prefix, 445217498156⟩,
    ⟨[1, 2, 0, 1], .prefix, 364144975506⟩,
    ⟨[1, 2, 0, 2], .prefix, 445217498156⟩,
    ⟨[1, 2, 0, 3], .prefix, 691501496481⟩,
    ⟨[1, 2, 1], .prefix, 359922431200⟩,
    ⟨[1, 2, 2], .prefix, 523731808018⟩,
    ⟨[1, 2, 3], .prefix, 632140515688⟩,
    ⟨[1, 2, 4], .prefix, 799042699168⟩,
    ⟨[1, 3, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 3, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 3, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[1, 3, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[1, 3, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[1, 3, 0, 0, 0, 2, 1], .prefix, 1477526532451⟩,
    ⟨[1, 3, 0, 0, 1, 0, 0], .kernel, 399225382291⟩,
    ⟨[1, 3, 0, 0, 1, 0, 1], .prefix, 959606511163⟩,
    ⟨[1, 3, 0, 0, 1, 1], .prefix, 936655214923⟩,
    ⟨[1, 3, 0, 0, 1, 2], .prefix, 1387225537268⟩,
    ⟨[1, 3, 0, 0, 2], .prefix, 626043142126⟩,
    ⟨[1, 3, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 3, 0, 1, 0, 0, 1], .prefix, 959606511163⟩,
    ⟨[1, 3, 0, 1, 0, 1], .prefix, 936655214923⟩,
    ⟨[1, 3, 0, 1, 0, 2], .prefix, 1387225537268⟩,
    ⟨[1, 3, 0, 1, 1], .prefix, 908261571109⟩,
    ⟨[1, 3, 0, 1, 2], .prefix, 1252086284252⟩,
    ⟨[1, 3, 0, 2], .prefix, 626043142126⟩,
    ⟨[1, 3, 0, 3], .prefix, 908261571109⟩,
    ⟨[1, 3, 1], .prefix, 421065837717⟩,
    ⟨[1, 3, 2], .prefix, 691501496481⟩,
    ⟨[1, 3, 3], .prefix, 835844634809⟩,
    ⟨[1, 3, 4], .prefix, 1047109123217⟩,
    ⟨[1, 4, 0, 0, 0, 0, 0], .kernel, 307427404842⟩,
    ⟨[1, 4, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 4, 0, 0, 0, 1, 0], .kernel, 613797494264⟩,
    ⟨[1, 4, 0, 0, 0, 1, 1], .prefix, 1207090873687⟩,
    ⟨[1, 4, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[1, 4, 0, 0, 0, 2, 1], .prefix, 1791500564014⟩,
    ⟨[1, 4, 0, 0, 1], .prefix, 572510239417⟩,
    ⟨[1, 4, 0, 0, 2], .prefix, 769186059629⟩,
    ⟨[1, 4, 0, 1], .prefix, 572510239417⟩,
    ⟨[1, 4, 0, 2], .prefix, 769186059629⟩,
    ⟨[1, 4, 0, 3], .prefix, 1075556149051⟩,
    ⟨[1, 4, 1], .prefix, 563626550321⟩,
    ⟨[1, 4, 2], .prefix, 809362473662⟩,
    ⟨[1, 4, 3], .prefix, 1047109123217⟩,
    ⟨[1, 4, 4], .prefix, 1281062132965⟩,
    ⟨[1, 5], .prefix, 364144975506⟩,
    ⟨[1, 6], .prefix, 390627136653⟩,
    ⟨[1, 7], .prefix, 421065837717⟩,
    ⟨[2, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 0, 1, 0], .kernel, 176603243038⟩,
    ⟨[2, 0, 0, 0, 0, 1, 1], .prefix, 364144975506⟩,
    ⟨[2, 0, 0, 0, 0, 2, 0], .kernel, 244854884809⟩,
    ⟨[2, 0, 0, 0, 0, 2, 1], .kernel, 404498823724⟩,
    ⟨[2, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 0, 0, 1, 0, 1], .prefix, 369374700711⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block06
