/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block07
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block07.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block07

def certificates : List ResidueTerminal :=
  [
    ⟨[2, 0, 0, 0, 1, 1], .prefix, 353825201012⟩,
    ⟨[2, 0, 0, 0, 1, 2], .prefix, 523731808018⟩,
    ⟨[2, 0, 0, 0, 2], .prefix, 222608749078⟩,
    ⟨[2, 0, 0, 1, 0, 0, 0], .kernel, 173866918651⟩,
    ⟨[2, 0, 0, 1, 0, 0, 1], .prefix, 369374700711⟩,
    ⟨[2, 0, 0, 1, 0, 1], .prefix, 353825201012⟩,
    ⟨[2, 0, 0, 1, 0, 2], .prefix, 523731808018⟩,
    ⟨[2, 0, 0, 1, 1], .prefix, 359922431200⟩,
    ⟨[2, 0, 0, 1, 2], .prefix, 445217498156⟩,
    ⟨[2, 0, 0, 2], .prefix, 222608749078⟩,
    ⟨[2, 0, 0, 3], .prefix, 359922431200⟩,
    ⟨[2, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 1, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[2, 0, 1, 0, 0, 1], .prefix, 346509850044⟩,
    ⟨[2, 0, 1, 0, 0, 2], .prefix, 526824614680⟩,
    ⟨[2, 0, 1, 0, 1], .prefix, 359054926217⟩,
    ⟨[2, 0, 1, 0, 2], .prefix, 445217498156⟩,
    ⟨[2, 0, 1, 1], .prefix, 359054926217⟩,
    ⟨[2, 0, 1, 2], .prefix, 445217498156⟩,
    ⟨[2, 0, 1, 3], .prefix, 687278952175⟩,
    ⟨[2, 0, 2, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 0, 2, 0, 0, 0, 1], .prefix, 542374114379⟩,
    ⟨[2, 0, 2, 0, 0, 1], .prefix, 523113093082⟩,
    ⟨[2, 0, 2, 0, 0, 2], .prefix, 737755792568⟩,
    ⟨[2, 0, 2, 0, 1], .prefix, 526824614680⟩,
    ⟨[2, 0, 2, 0, 2], .prefix, 667826247234⟩,
    ⟨[2, 0, 2, 1], .prefix, 526824614680⟩,
    ⟨[2, 0, 2, 2], .prefix, 667826247234⟩,
    ⟨[2, 0, 2, 3], .prefix, 964726761868⟩,
    ⟨[2, 0, 3], .prefix, 346509850044⟩,
    ⟨[2, 0, 4], .prefix, 406795442223⟩,
    ⟨[2, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 1, 0, 0, 0, 0, 1], .prefix, 364144975506⟩,
    ⟨[2, 1, 0, 0, 0, 1], .prefix, 365012480489⟩,
    ⟨[2, 1, 0, 0, 0, 2], .prefix, 542234438463⟩,
    ⟨[2, 1, 0, 0, 1], .prefix, 353825201012⟩,
    ⟨[2, 1, 0, 0, 2], .prefix, 445217498156⟩,
    ⟨[2, 1, 0, 1], .prefix, 353825201012⟩,
    ⟨[2, 1, 0, 2], .prefix, 445217498156⟩,
    ⟨[2, 1, 0, 3], .prefix, 632140515688⟩,
    ⟨[2, 1, 1], .prefix, 346509850044⟩,
    ⟨[2, 1, 2], .prefix, 523113093082⟩,
    ⟨[2, 1, 3], .prefix, 676602695406⟩,
    ⟨[2, 1, 4], .prefix, 792594853183⟩,
    ⟨[2, 2, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 2, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[2, 2, 0, 0, 0, 1], .prefix, 542234438463⟩,
    ⟨[2, 2, 0, 0, 0, 2], .prefix, 824204168334⟩,
    ⟨[2, 2, 0, 0, 1], .prefix, 523731808018⟩,
    ⟨[2, 2, 0, 0, 2], .prefix, 667826247234⟩,
    ⟨[2, 2, 0, 1], .prefix, 523731808018⟩,
    ⟨[2, 2, 0, 2], .prefix, 667826247234⟩,
    ⟨[2, 2, 0, 3], .prefix, 983229392313⟩,
    ⟨[2, 2, 1], .prefix, 526824614680⟩,
    ⟨[2, 2, 2], .prefix, 737755792568⟩,
    ⟨[2, 2, 3], .prefix, 961365856067⟩,
    ⟨[2, 2, 4], .prefix, 1190939340316⟩,
    ⟨[2, 3], .prefix, 364144975506⟩,
    ⟨[2, 4, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[2, 4, 0, 0, 0, 0, 1], .prefix, 891837095169⟩,
    ⟨[2, 4, 0, 0, 0, 1], .prefix, 872327283825⟩,
    ⟨[2, 4, 0, 0, 0, 2], .prefix, 1295271631591⟩,
    ⟨[2, 4, 0, 0, 1], .prefix, 809362473662⟩,
    ⟨[2, 4, 0, 0, 2], .prefix, 1113043745390⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block07
