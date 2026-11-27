/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block05
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block05.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block05

def certificates : List ResidueTerminal :=
  [
    ⟨[1, 0, 0, 1, 1, 1], .prefix, 466529274077⟩,
    ⟨[1, 0, 0, 1, 1, 2], .prefix, 691501496481⟩,
    ⟨[1, 0, 0, 1, 2], .prefix, 361651287940⟩,
    ⟨[1, 0, 0, 2], .prefix, 180825643970⟩,
    ⟨[1, 0, 0, 3, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 3, 0, 0, 1], .kernel, 478258518902⟩,
    ⟨[1, 0, 0, 3, 0, 1], .prefix, 466529274077⟩,
    ⟨[1, 0, 0, 3, 0, 2], .prefix, 691501496481⟩,
    ⟨[1, 0, 0, 3, 1, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 0, 3, 1, 0, 1], .prefix, 921271862833⟩,
    ⟨[1, 0, 0, 3, 1, 1], .prefix, 916042137628⟩,
    ⟨[1, 0, 0, 3, 1, 2], .prefix, 1254579971818⟩,
    ⟨[1, 0, 0, 3, 2], .prefix, 723302575880⟩,
    ⟨[1, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 0, 1, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[1, 0, 1, 0, 0, 1], .prefix, 212537673696⟩,
    ⟨[1, 0, 1, 0, 0, 2], .prefix, 359922431200⟩,
    ⟨[1, 0, 1, 0, 1, 0, 0], .kernel, 237327344766⟩,
    ⟨[1, 0, 1, 0, 1, 0, 1], .kernel, 452358562654⟩,
    ⟨[1, 0, 1, 0, 1, 1], .prefix, 423396481799⟩,
    ⟨[1, 0, 1, 0, 1, 2], .prefix, 631273010705⟩,
    ⟨[1, 0, 1, 0, 2], .prefix, 323968561473⟩,
    ⟨[1, 0, 1, 1, 0, 0, 0], .kernel, 208365263911⟩,
    ⟨[1, 0, 1, 1, 0, 0, 1], .kernel, 405110657713⟩,
    ⟨[1, 0, 1, 1, 0, 1], .prefix, 423396481799⟩,
    ⟨[1, 0, 1, 1, 0, 2], .prefix, 631273010705⟩,
    ⟨[1, 0, 1, 1, 1], .prefix, 471758999282⟩,
    ⟨[1, 0, 1, 1, 2], .prefix, 647937122946⟩,
    ⟨[1, 0, 1, 2], .prefix, 323968561473⟩,
    ⟨[1, 0, 1, 3], .prefix, 471758999282⟩,
    ⟨[1, 0, 2, 0, 0, 0, 0], .kernel, 167769688463⟩,
    ⟨[1, 0, 2, 0, 0, 0, 1], .prefix, 369374700711⟩,
    ⟨[1, 0, 2, 0, 0, 1], .prefix, 353825201012⟩,
    ⟨[1, 0, 2, 0, 0, 2], .prefix, 523731808018⟩,
    ⟨[1, 0, 2, 0, 1], .prefix, 359922431200⟩,
    ⟨[1, 0, 2, 0, 2], .prefix, 445217498156⟩,
    ⟨[1, 0, 2, 1], .prefix, 359922431200⟩,
    ⟨[1, 0, 2, 2], .prefix, 445217498156⟩,
    ⟨[1, 0, 2, 3], .prefix, 631273010705⟩,
    ⟨[1, 0, 3], .prefix, 212537673696⟩,
    ⟨[1, 0, 4], .prefix, 302147545116⟩,
    ⟨[1, 1, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[1, 1, 0, 0, 0, 0, 1], .kernel, 238600673428⟩,
    ⟨[1, 1, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[1, 1, 0, 0, 0, 1, 1], .kernel, 465418433263⟩,
    ⟨[1, 1, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[1, 1, 0, 0, 0, 2, 1], .kernel, 603208526577⟩,
    ⟨[1, 1, 0, 0, 1, 0, 0], .kernel, 217817533422⟩,
    ⟨[1, 1, 0, 0, 1, 0, 1], .kernel, 427619026105⟩,
    ⟨[1, 1, 0, 0, 1, 1], .prefix, 485922548104⟩,
    ⟨[1, 1, 0, 0, 1, 2], .prefix, 718837681501⟩,
    ⟨[1, 1, 0, 0, 2], .prefix, 323968561473⟩,
    ⟨[1, 1, 0, 1, 0, 0, 0], .kernel, 240931174136⟩,
    ⟨[1, 1, 0, 1, 0, 0, 1], .kernel, 377448082162⟩,
    ⟨[1, 1, 0, 1, 0, 1], .prefix, 485922548104⟩,
    ⟨[1, 1, 0, 1, 0, 2], .prefix, 718837681501⟩,
    ⟨[1, 1, 0, 1, 1], .prefix, 466529274077⟩,
    ⟨[1, 1, 0, 1, 2], .prefix, 647937122946⟩,
    ⟨[1, 1, 0, 2], .prefix, 323968561473⟩,
    ⟨[1, 1, 0, 3], .prefix, 466529274077⟩,
    ⟨[1, 1, 1], .prefix, 212537673696⟩,
    ⟨[1, 1, 2], .prefix, 353825201012⟩,
    ⟨[1, 1, 3], .prefix, 424669667087⟩,
    ⟨[1, 1, 4], .prefix, 550213969165⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block05
