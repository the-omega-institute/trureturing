/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block01
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Block01.chunk_checked
   digest: Complete arithmetic for one block of nineteen-tree terminals. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19.Initial

/-! This module checks the complete arithmetic of every listed terminal exactly once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block01

def certificates : List ResidueTerminal :=
  [
    ⟨[0, 0, 1, 0, 1, 1, 0], .kernel, 188723199837⟩,
    ⟨[0, 0, 1, 0, 1, 1, 1], .prefix, 423396481799⟩,
    ⟨[0, 0, 1, 0, 1, 2], .prefix, 346509850044⟩,
    ⟨[0, 0, 1, 0, 2], .prefix, 180825643970⟩,
    ⟨[0, 0, 1, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 1, 0, 0, 1], .kernel, 208365263911⟩,
    ⟨[0, 0, 1, 1, 0, 1, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 1, 0, 1, 1], .prefix, 423396481799⟩,
    ⟨[0, 0, 1, 1, 0, 2], .prefix, 346509850044⟩,
    ⟨[0, 0, 1, 1, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 1, 1, 0, 1], .prefix, 471758999282⟩,
    ⟨[0, 0, 1, 1, 1, 1], .prefix, 459213923109⟩,
    ⟨[0, 0, 1, 1, 1, 2], .prefix, 629404191301⟩,
    ⟨[0, 0, 1, 1, 2], .prefix, 361651287940⟩,
    ⟨[0, 0, 1, 2], .prefix, 180825643970⟩,
    ⟨[0, 0, 1, 3, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 3, 0, 0, 1], .prefix, 471758999282⟩,
    ⟨[0, 0, 1, 3, 0, 1], .prefix, 459213923109⟩,
    ⟨[0, 0, 1, 3, 0, 2], .prefix, 629404191301⟩,
    ⟨[0, 0, 1, 3, 1, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 1, 3, 1, 0, 1], .prefix, 911819593322⟩,
    ⟨[0, 0, 1, 3, 1, 1], .prefix, 901143336553⟩,
    ⟨[0, 0, 1, 3, 1, 2], .prefix, 1236944846356⟩,
    ⟨[0, 0, 1, 3, 2], .prefix, 723302575880⟩,
    ⟨[0, 0, 2, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 2, 0, 0, 0, 1], .kernel, 167769688463⟩,
    ⟨[0, 0, 2, 0, 0, 1, 0], .kernel, 169638507867⟩,
    ⟨[0, 0, 2, 0, 0, 1, 1], .prefix, 353825201012⟩,
    ⟨[0, 0, 2, 0, 0, 2, 0], .kernel, 229924100046⟩,
    ⟨[0, 0, 2, 0, 0, 2, 1], .prefix, 523731808018⟩,
    ⟨[0, 0, 2, 0, 1], .prefix, 184186693145⟩,
    ⟨[0, 0, 2, 0, 2], .prefix, 222608749078⟩,
    ⟨[0, 0, 2, 1], .prefix, 184186693145⟩,
    ⟨[0, 0, 2, 2], .prefix, 222608749078⟩,
    ⟨[0, 0, 2, 3], .prefix, 346509850044⟩,
    ⟨[0, 0, 3, 0, 0, 0, 0], .kernel, 117960851971⟩,
    ⟨[0, 0, 3, 0, 0, 0, 1], .prefix, 212537673696⟩,
    ⟨[0, 0, 3, 0, 0, 1, 0], .kernel, 190186338936⟩,
    ⟨[0, 0, 3, 0, 0, 1, 1], .prefix, 424669667087⟩,
    ⟨[0, 0, 3, 0, 0, 2], .prefix, 347377355027⟩,
    ⟨[0, 0, 3, 0, 1, 0, 0], .kernel, 188723199837⟩,
    ⟨[0, 0, 3, 0, 1, 0, 1], .prefix, 423396481799⟩,
    ⟨[0, 0, 3, 0, 1, 1], .prefix, 477988482200⟩,
    ⟨[0, 0, 3, 0, 1, 2], .prefix, 676602695406⟩,
    ⟨[0, 0, 3, 0, 2], .prefix, 323968561473⟩,
    ⟨[0, 0, 3, 1, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 3, 1, 0, 0, 1], .prefix, 423396481799⟩,
    ⟨[0, 0, 3, 1, 0, 1], .prefix, 477988482200⟩,
    ⟨[0, 0, 3, 1, 0, 2], .prefix, 676602695406⟩,
    ⟨[0, 0, 3, 1, 1], .prefix, 459213923109⟩,
    ⟨[0, 0, 3, 1, 2], .prefix, 647937122946⟩,
    ⟨[0, 0, 3, 2], .prefix, 323968561473⟩,
    ⟨[0, 0, 3, 3], .prefix, 459213923109⟩,
    ⟨[0, 0, 4, 0, 0, 0, 0], .direct, 0⟩,
    ⟨[0, 0, 4, 0, 0, 0, 1], .prefix, 302147545116⟩,
    ⟨[0, 0, 4, 0, 0, 1, 0], .kernel, 240400855733⟩,
    ⟨[0, 0, 4, 0, 0, 1, 1], .prefix, 550213969165⟩,
    ⟨[0, 0, 4, 0, 0, 2], .prefix, 453993946328⟩,
    ⟨[0, 0, 4, 0, 1], .prefix, 307214370211⟩,
    ⟨[0, 0, 4, 0, 2], .prefix, 403434393048⟩,
    ⟨[0, 0, 4, 1], .prefix, 307214370211⟩,
    ⟨[0, 0, 4, 2], .prefix, 403434393048⟩,
    ⟨[0, 0, 4, 3], .prefix, 560265501146⟩,
    ⟨[0, 1, 0, 0, 0, 0, 0], .direct, 0⟩
  ]

theorem chunk_checked :
    certificates.all (checkResidueTerminal 19 2 4294967296 initialVector) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19.Block01
