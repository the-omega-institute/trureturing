/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block03
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block03.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block03

def certificates : List ResidueTerminal :=
  [
    ⟨[0, 1, 3, 0, 0, 1], .prefix, 482622716663⟩,
    ⟨[0, 1, 3, 0, 0, 2], .prefix, 686303754964⟩,
    ⟨[0, 1, 3, 0, 1], .prefix, 477988482200⟩,
    ⟨[0, 1, 3, 0, 2], .prefix, 626043142126⟩,
    ⟨[0, 1, 3, 1], .prefix, 477988482200⟩,
    ⟨[0, 1, 3, 2], .prefix, 626043142126⟩,
    ⟨[0, 1, 3, 3], .prefix, 883042995540⟩,
    ⟨[0, 1, 4, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 1, 4, 0, 0, 0, 1], .prefix, 550213969165⟩,
    ⟨[0, 1, 4, 0, 0, 1], .prefix, 605840347540⟩,
    ⟨[0, 1, 4, 0, 0, 2], .prefix, 847376807395⟩,
    ⟨[0, 1, 4, 0, 1], .prefix, 563708668530⟩,
    ⟨[0, 1, 4, 0, 2], .prefix, 769186059629⟩,
    ⟨[0, 1, 4, 1], .prefix, 563708668530⟩,
    ⟨[0, 1, 4, 2], .prefix, 769186059629⟩,
    ⟨[0, 1, 4, 3], .prefix, 1056434803670⟩,
    ⟨[0, 2, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 0, 2, 1], .direct, 0⟩,
    ⟨[0, 2, 0, 0, 1, 0, 0], .kernel, 159586832512⟩,
    ⟨[0, 2, 0, 0, 1, 0, 1], .prefix, 364144975506⟩,
    ⟨[0, 2, 0, 0, 1, 1], .prefix, 365012480489⟩,
    ⟨[0, 2, 0, 0, 1, 2], .prefix, 542234438463⟩,
    ⟨[0, 2, 0, 0, 2], .prefix, 222608749078⟩,
    ⟨[0, 2, 0, 1, 0, 0, 0], .kernel, 178089462957⟩,
    ⟨[0, 2, 0, 1, 0, 0, 1], .prefix, 364144975506⟩,
    ⟨[0, 2, 0, 1, 0, 1], .prefix, 365012480489⟩,
    ⟨[0, 2, 0, 1, 0, 2], .prefix, 542234438463⟩,
    ⟨[0, 2, 0, 1, 1], .prefix, 353825201012⟩,
    ⟨[0, 2, 0, 1, 2], .prefix, 445217498156⟩,
    ⟨[0, 2, 0, 2], .prefix, 222608749078⟩,
    ⟨[0, 2, 0, 3], .prefix, 353825201012⟩,
    ⟨[0, 2, 1], .prefix, 184186693145⟩,
    ⟨[0, 2, 2, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 2, 2, 0, 0, 0, 1], .prefix, 523731808018⟩,
    ⟨[0, 2, 2, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 2, 2, 0, 0, 1, 1], .prefix, 1031914116337⟩,
    ⟨[0, 2, 2, 0, 0, 2], .prefix, 801990016291⟩,
    ⟨[0, 2, 2, 0, 1], .prefix, 523113093082⟩,
    ⟨[0, 2, 2, 0, 2], .prefix, 667826247234⟩,
    ⟨[0, 2, 2, 1], .prefix, 523113093082⟩,
    ⟨[0, 2, 2, 2], .prefix, 667826247234⟩,
    ⟨[0, 2, 2, 3], .prefix, 961365856067⟩,
    ⟨[0, 2, 3], .prefix, 347377355027⟩,
    ⟨[0, 2, 4], .prefix, 453993946328⟩,
    ⟨[0, 3, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 3, 0, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 3, 0, 0, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 3, 0, 0, 0, 1, 1], .direct, 0⟩,
    ⟨[0, 3, 0, 0, 0, 2, 0], .direct, 0⟩,
    ⟨[0, 3, 0, 0, 0, 2, 1], .direct, 0⟩,
    ⟨[0, 3, 0, 0, 1, 0, 0], .kernel, 181407848869⟩,
    ⟨[0, 3, 0, 0, 1, 0, 1], .kernel, 399225382291⟩,
    ⟨[0, 3, 0, 0, 1, 1], .prefix, 485922548104⟩,
    ⟨[0, 3, 0, 0, 1, 2], .prefix, 718837681501⟩,
    ⟨[0, 3, 0, 0, 2], .prefix, 323968561473⟩,
    ⟨[0, 3, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 3, 0, 1, 0, 0, 1], .direct, 0⟩,
    ⟨[0, 3, 0, 1, 0, 1], .prefix, 485922548104⟩,
    ⟨[0, 3, 0, 1, 0, 2], .prefix, 718837681501⟩,
    ⟨[0, 3, 0, 1, 1], .prefix, 466529274077⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block03
