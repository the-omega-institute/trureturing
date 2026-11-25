/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block08
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block08.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block08

def certificates : List ResidueTerminal :=
  [
    ⟨[2, 4, 0, 1], .prefix, 809362473662⟩,
    ⟨[2, 4, 0, 2], .prefix, 1113043745390⟩,
    ⟨[2, 4, 0, 3], .prefix, 1581936492793⟩,
    ⟨[2, 4, 1], .prefix, 805139929356⟩,
    ⟨[2, 4, 2], .prefix, 1191558055252⟩,
    ⟨[2, 4, 3], .prefix, 1522575512000⟩,
    ⟨[2, 4, 4], .prefix, 1912086444558⟩,
    ⟨[2, 5], .prefix, 523731808018⟩,
    ⟨[2, 6], .prefix, 576433950090⟩,
    ⟨[2, 7], .prefix, 631273010705⟩,
    ⟨[3, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[3, 0, 0, 0, 0, 0, 1], .kernel, 241499754551⟩,
    ⟨[3, 0, 0, 0, 0, 1], .prefix, 212537673696⟩,
    ⟨[3, 0, 0, 0, 0, 2], .prefix, 359922431200⟩,
    ⟨[3, 0, 0, 0, 1, 0, 0], .kernel, 207876528906⟩,
    ⟨[3, 0, 0, 0, 1, 0, 1], .kernel, 366333081535⟩,
    ⟨[3, 0, 0, 0, 1, 1], .prefix, 423396481799⟩,
    ⟨[3, 0, 0, 0, 1, 2], .prefix, 631273010705⟩,
    ⟨[3, 0, 0, 0, 2], .prefix, 323968561473⟩,
    ⟨[3, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[3, 0, 0, 1, 0, 0, 1], .direct, 0⟩,
    ⟨[3, 0, 0, 1, 0, 1], .prefix, 423396481799⟩,
    ⟨[3, 0, 0, 1, 0, 2], .prefix, 631273010705⟩,
    ⟨[3, 0, 0, 1, 1], .prefix, 471758999282⟩,
    ⟨[3, 0, 0, 1, 2], .prefix, 647937122946⟩,
    ⟨[3, 0, 0, 2], .prefix, 323968561473⟩,
    ⟨[3, 0, 0, 3], .prefix, 471758999282⟩,
    ⟨[3, 0, 1, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[3, 0, 1, 0, 0, 0, 1], .direct, 0⟩,
    ⟨[3, 0, 1, 0, 0, 1], .prefix, 423802162104⟩,
    ⟨[3, 0, 1, 0, 0, 2], .prefix, 687278952175⟩,
    ⟨[3, 0, 1, 0, 1], .prefix, 478913688264⟩,
    ⟨[3, 0, 1, 0, 2], .prefix, 626043142126⟩,
    ⟨[3, 0, 1, 1], .prefix, 478913688264⟩,
    ⟨[3, 0, 1, 2], .prefix, 626043142126⟩,
    ⟨[3, 0, 1, 3], .prefix, 917451607959⟩,
    ⟨[3, 0, 2], .prefix, 359054926217⟩,
    ⟨[3, 0, 3], .prefix, 423802162104⟩,
    ⟨[3, 0, 4], .prefix, 543660924151⟩,
    ⟨[3, 1], .prefix, 212537673696⟩,
    ⟨[3, 2], .prefix, 359922431200⟩,
    ⟨[3, 3], .prefix, 421065837717⟩,
    ⟨[3, 4], .prefix, 563626550321⟩,
    ⟨[3, 5], .prefix, 631273010705⟩,
    ⟨[3, 6], .prefix, 747365043272⟩,
    ⟨[3, 7], .prefix, 841074360014⟩,
    ⟨[4, 0, 0, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[4, 0, 0, 0, 0, 0, 1], .kernel, 279764829291⟩,
    ⟨[4, 0, 0, 0, 0, 1], .prefix, 302147545116⟩,
    ⟨[4, 0, 0, 0, 0, 2], .prefix, 408664261627⟩,
    ⟨[4, 0, 0, 0, 1, 0, 0], .kernel, 248472104354⟩,
    ⟨[4, 0, 0, 0, 1, 0, 1], .prefix, 614971347001⟩,
    ⟨[4, 0, 0, 0, 1, 1], .prefix, 536100554864⟩,
    ⟨[4, 0, 0, 0, 1, 2], .prefix, 805139929356⟩,
    ⟨[4, 0, 0, 0, 2], .prefix, 403434393048⟩,
    ⟨[4, 0, 0, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[4, 0, 0, 1, 0, 0, 1], .prefix, 614971347001⟩,
    ⟨[4, 0, 0, 1, 0, 1], .prefix, 536100554864⟩,
    ⟨[4, 0, 0, 1, 0, 2], .prefix, 805139929356⟩,
    ⟨[4, 0, 0, 1, 1], .prefix, 576682505828⟩,
    ⟨[4, 0, 0, 1, 2], .prefix, 806868786096⟩,
    ⟨[4, 0, 0, 2], .prefix, 403434393048⟩,
    ⟨[4, 0, 0, 3], .prefix, 576682505828⟩,
    ⟨[4, 0, 1, 0, 0, 0, 0], .direct, 0⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block08
