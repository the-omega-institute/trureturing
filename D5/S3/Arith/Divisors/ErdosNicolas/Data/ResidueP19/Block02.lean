/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block02
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block02.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block02

def certificates : List ResidueTerminal :=
  [
    ⟨[0, 1, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 0, 2, 1], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 0, 1, 0, 1], .kernel, 217817533422⟩,
    ⟨[0, 1, 0, 0, 1, 1, 0], .kernel, 243505154049⟩,
    ⟨[0, 1, 0, 0, 1, 1, 1], .prefix, 485922548104⟩,
    ⟨[0, 1, 0, 0, 1, 2], .prefix, 365012480489⟩,
    ⟨[0, 1, 0, 0, 2], .prefix, 180825643970⟩,
    ⟨[0, 1, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 1, 0, 0, 1], .kernel, 240931174136⟩,
    ⟨[0, 1, 0, 1, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 1, 0, 1, 1], .prefix, 485922548104⟩,
    ⟨[0, 1, 0, 1, 0, 2], .prefix, 365012480489⟩,
    ⟨[0, 1, 0, 1, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 1, 1, 0, 1], .prefix, 466529274077⟩,
    ⟨[0, 1, 0, 1, 1, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 1, 1, 1, 1], .prefix, 925277981635⟩,
    ⟨[0, 1, 0, 1, 1, 2], .prefix, 694237820868⟩,
    ⟨[0, 1, 0, 1, 2], .prefix, 361651287940⟩,
    ⟨[0, 1, 0, 2], .prefix, 180825643970⟩,
    ⟨[0, 1, 0, 3, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 3, 0, 0, 1], .prefix, 466529274077⟩,
    ⟨[0, 1, 0, 3, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 0, 3, 0, 1, 1], .prefix, 925277981635⟩,
    ⟨[0, 1, 0, 3, 0, 2], .prefix, 694237820868⟩,
    ⟨[0, 1, 0, 3, 1, 0, 0], .kernel, 492262415113⟩,
    ⟨[0, 1, 0, 3, 1, 0, 1], .prefix, 916042137628⟩,
    ⟨[0, 1, 0, 3, 1, 1], .prefix, 925743197186⟩,
    ⟨[0, 1, 0, 3, 1, 2], .prefix, 1255447476801⟩,
    ⟨[0, 1, 0, 3, 2], .prefix, 723302575880⟩,
    ⟨[0, 1, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 1, 0, 0, 0, 1], .prefix, 212537673696⟩,
    ⟨[0, 1, 1, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 1, 0, 0, 1, 1], .prefix, 424669667087⟩,
    ⟨[0, 1, 1, 0, 0, 2], .prefix, 347377355027⟩,
    ⟨[0, 1, 1, 0, 1, 0, 0], .kernel, 216331313503⟩,
    ⟨[0, 1, 1, 0, 1, 0, 1], .prefix, 423396481799⟩,
    ⟨[0, 1, 1, 0, 1, 1], .prefix, 477988482200⟩,
    ⟨[0, 1, 1, 0, 1, 2], .prefix, 676602695406⟩,
    ⟨[0, 1, 1, 0, 2], .prefix, 323968561473⟩,
    ⟨[0, 1, 1, 1, 0, 0, 0], .kernel, 224782268593⟩,
    ⟨[0, 1, 1, 1, 0, 0, 1], .prefix, 423396481799⟩,
    ⟨[0, 1, 1, 1, 0, 1], .prefix, 477988482200⟩,
    ⟨[0, 1, 1, 1, 0, 2], .prefix, 676602695406⟩,
    ⟨[0, 1, 1, 1, 1], .prefix, 459213923109⟩,
    ⟨[0, 1, 1, 1, 2], .prefix, 647937122946⟩,
    ⟨[0, 1, 1, 2], .prefix, 323968561473⟩,
    ⟨[0, 1, 1, 3], .prefix, 459213923109⟩,
    ⟨[0, 1, 2, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 2, 0, 0, 0, 1], .prefix, 353825201012⟩,
    ⟨[0, 1, 2, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 1, 2, 0, 0, 1, 1], .prefix, 694237820868⟩,
    ⟨[0, 1, 2, 0, 0, 2, 0], .kernel, 523463708879⟩,
    ⟨[0, 1, 2, 0, 0, 2, 1], .prefix, 1031914116337⟩,
    ⟨[0, 1, 2, 0, 1], .prefix, 347377355027⟩,
    ⟨[0, 1, 2, 0, 2], .prefix, 445217498156⟩,
    ⟨[0, 1, 2, 1], .prefix, 347377355027⟩,
    ⟨[0, 1, 2, 2], .prefix, 445217498156⟩,
    ⟨[0, 1, 2, 3], .prefix, 676602695406⟩,
    ⟨[0, 1, 3, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 3, 0, 0, 0, 1], .prefix, 424669667087⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block02
