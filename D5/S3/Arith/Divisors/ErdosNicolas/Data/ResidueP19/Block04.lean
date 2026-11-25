/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block04
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block04.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block04

def certificates : List ResidueTerminal :=
  [
    ⟨[0, 3, 0, 1, 2], .prefix, 647937122946⟩,
    ⟨[0, 3, 0, 2], .prefix, 323968561473⟩,
    ⟨[0, 3, 0, 3], .prefix, 466529274077⟩,
    ⟨[0, 3, 1], .prefix, 212537673696⟩,
    ⟨[0, 3, 2], .prefix, 353825201012⟩,
    ⟨[0, 3, 3], .prefix, 424669667087⟩,
    ⟨[0, 3, 4], .prefix, 550213969165⟩,
    ⟨[0, 4, 0, 0, 0, 0, 0], .kernel, 140682202555⟩,
    ⟨[0, 4, 0, 0, 0, 0, 1], .kernel, 307427404842⟩,
    ⟨[0, 4, 0, 0, 0, 1, 0], .kernel, 279033904402⟩,
    ⟨[0, 4, 0, 0, 0, 1, 1], .kernel, 613797494264⟩,
    ⟨[0, 4, 0, 0, 0, 2, 0], .kernel, 445779106689⟩,
    ⟨[0, 4, 0, 0, 0, 2, 1], .direct, 0⟩,
    ⟨[0, 4, 0, 0, 1, 0, 0], .kernel, 235416005473⟩,
    ⟨[0, 4, 0, 0, 1, 0, 1], .prefix, 572510239417⟩,
    ⟨[0, 4, 0, 0, 1, 1], .prefix, 608517634538⟩,
    ⟨[0, 4, 0, 0, 1, 2], .prefix, 872327283825⟩,
    ⟨[0, 4, 0, 0, 2], .prefix, 403434393048⟩,
    ⟨[0, 4, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 4, 0, 1, 0, 0, 1], .prefix, 572510239417⟩,
    ⟨[0, 4, 0, 1, 0, 1], .prefix, 608517634538⟩,
    ⟨[0, 4, 0, 1, 0, 2], .prefix, 872327283825⟩,
    ⟨[0, 4, 0, 1, 1], .prefix, 571452780623⟩,
    ⟨[0, 4, 0, 1, 2], .prefix, 806868786096⟩,
    ⟨[0, 4, 0, 2], .prefix, 403434393048⟩,
    ⟨[0, 4, 0, 3], .prefix, 571452780623⟩,
    ⟨[0, 4, 1], .prefix, 302147545116⟩,
    ⟨[0, 4, 2], .prefix, 409531766610⟩,
    ⟨[0, 4, 3], .prefix, 550213969165⟩,
    ⟨[0, 4, 4], .prefix, 647278416165⟩,
    ⟨[0, 5, 0, 0, 0, 0, 0], .kernel, 159586832512⟩,
    ⟨[0, 5, 0, 0, 0, 0, 1], .prefix, 364144975506⟩,
    ⟨[0, 5, 0, 0, 0, 1], .prefix, 365012480489⟩,
    ⟨[0, 5, 0, 0, 0, 2], .prefix, 542234438463⟩,
    ⟨[0, 5, 0, 0, 1], .prefix, 353825201012⟩,
    ⟨[0, 5, 0, 0, 2], .prefix, 445217498156⟩,
    ⟨[0, 5, 0, 1], .prefix, 353825201012⟩,
    ⟨[0, 5, 0, 2], .prefix, 445217498156⟩,
    ⟨[0, 5, 0, 3], .prefix, 632140515688⟩,
    ⟨[0, 5, 1], .prefix, 346509850044⟩,
    ⟨[0, 5, 2], .prefix, 523113093082⟩,
    ⟨[0, 5, 3], .prefix, 676602695406⟩,
    ⟨[0, 5, 4], .prefix, 792594853183⟩,
    ⟨[0, 6], .prefix, 202060918009⟩,
    ⟨[0, 7], .prefix, 212537673696⟩,
    ⟨[1, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 1, 1], .kernel, 226817759835⟩,
    ⟨[1, 0, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 0, 2, 1], .kernel, 313974031563⟩,
    ⟨[1, 0, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 1, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 1, 1, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 1, 1, 1], .direct, 0⟩,
    ⟨[1, 0, 0, 0, 1, 2], .prefix, 364144975506⟩,
    ⟨[1, 0, 0, 0, 2], .prefix, 180825643970⟩,
    ⟨[1, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 1, 0, 0, 1], .kernel, 227875075255⟩,
    ⟨[1, 0, 0, 1, 0, 1, 0], .kernel, 198424259395⟩,
    ⟨[1, 0, 0, 1, 0, 1, 1], .kernel, 343824713143⟩,
    ⟨[1, 0, 0, 1, 0, 2], .prefix, 364144975506⟩,
    ⟨[1, 0, 0, 1, 1, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 1, 1, 0, 1], .kernel, 478258518902⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block04
