/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Small00
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Small00.chunk_checked
   digest: Complete integer certificates for the first ten small exceptional lifts. -/

import D5.S3.Arith.Divisors.ErdosNicolas.FiniteChecker

/-! All rounded pair sums and complete divisor tables are checked in the kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas.Data.Small00

open D5.S3.Arith.ErdosNicolas

def certificates : List NumberCertificate :=
  [
    ⟨24, [(2, 3), (3, 1)],
      [1, 2, 3, 4, 6, 8, 12, 24]⟩,
    ⟨36, [(2, 2), (3, 2)],
      [1, 2, 3, 4, 6, 9, 12, 18, 36]⟩,
    ⟨48, [(2, 4), (3, 1)],
      [1, 2, 3, 4, 6, 8, 12, 16, 24, 48]⟩,
    ⟨60, [(2, 2), (3, 1), (5, 1)],
      [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60]⟩,
    ⟨72, [(2, 3), (3, 2)],
      [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]⟩,
    ⟨84, [(2, 2), (3, 1), (7, 1)],
      [1, 2, 3, 4, 6, 7, 12, 14, 21, 28, 42, 84]⟩,
    ⟨120, [(2, 3), (3, 1), (5, 1)],
      [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]⟩,
    ⟨132, [(2, 2), (3, 1), (11, 1)],
      [1, 2, 3, 4, 6, 11, 12, 22, 33, 44, 66, 132]⟩,
    ⟨156, [(2, 2), (3, 1), (13, 1)],
      [1, 2, 3, 4, 6, 12, 13, 26, 39, 52, 78, 156]⟩,
    ⟨168, [(2, 3), (3, 1), (7, 1)],
      [1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168]⟩
  ]

theorem chunk_checked : certificates.all (checkGood 4294967296) = true := by decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Small00
