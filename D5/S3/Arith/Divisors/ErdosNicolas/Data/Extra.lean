/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Extra
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Extra.extra_ok
   digest: Exact integer divisor certificates for the six additional targets. -/

import D5.S3.Arith.Divisors.ErdosNicolas.FiniteChecker
import D5.S3.Arith.Divisors.ErdosNicolas.Classification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas.Data.Extra

open D5.S3.Arith.ErdosNicolas

private def certificates : List NumberCertificate :=
  [
    ⟨625, [(5, 4)], [1, 5, 25, 125, 625]⟩,
    ⟨6875, [(5, 4), (11, 1)], [1, 5, 11, 25, 55, 125, 275, 625, 1375, 6875]⟩,
    ⟨343, [(7, 3)], [1, 7, 49, 343]⟩,
    ⟨4459, [(7, 3), (13, 1)], [1, 7, 13, 49, 91, 343, 637, 4459]⟩,
    ⟨121, [(11, 2)], [1, 11, 121]⟩,
    ⟨169, [(13, 2)], [1, 13, 169]⟩
  ]

private theorem chunk_checked : certificates.all (checkGood 4294967296) = true := by decide +kernel

private theorem values_eq : certifiedValues certificates = extraValues := by decide +kernel

theorem extra_ok : ExtraOK := by
  intro n hn
  exact good_of_mem_certifiedValues chunk_checked (by rwa [values_eq])

#print axioms chunk_checked
#print axioms extra_ok

end D5.S3.Arith.ErdosNicolas.Data.Extra
