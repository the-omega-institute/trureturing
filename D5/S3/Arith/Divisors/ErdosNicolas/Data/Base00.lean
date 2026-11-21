/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Base00
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Base00.chunk_checked,D5/S3/Arith/Divisors/ErdosNicolas/Data/Base00.good_on_interval
   digest: Complete integer divisor certificates on [1,65). -/

import D5.S3.Arith.Divisors.ErdosNicolas.FiniteChecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace D5.S3.Arith.ErdosNicolas.Data.Base00

open D5.S3.Arith.ErdosNicolas

private def certificates : List NumberCertificate :=
  [
    ⟨1, [], [1]⟩,
    ⟨2, [(2, 1)], [1, 2]⟩,
    ⟨3, [(3, 1)], [1, 3]⟩,
    ⟨4, [(2, 2)], [1, 2, 4]⟩,
    ⟨5, [(5, 1)], [1, 5]⟩,
    ⟨6, [(2, 1), (3, 1)], [1, 2, 3, 6]⟩,
    ⟨7, [(7, 1)], [1, 7]⟩,
    ⟨8, [(2, 3)], [1, 2, 4, 8]⟩,
    ⟨9, [(3, 2)], [1, 3, 9]⟩,
    ⟨10, [(2, 1), (5, 1)], [1, 2, 5, 10]⟩,
    ⟨11, [(11, 1)], [1, 11]⟩,
    ⟨12, [(2, 2), (3, 1)], [1, 2, 3, 4, 6, 12]⟩,
    ⟨13, [(13, 1)], [1, 13]⟩,
    ⟨14, [(2, 1), (7, 1)], [1, 2, 7, 14]⟩,
    ⟨15, [(3, 1), (5, 1)], [1, 3, 5, 15]⟩,
    ⟨16, [(2, 4)], [1, 2, 4, 8, 16]⟩,
    ⟨17, [(17, 1)], [1, 17]⟩,
    ⟨18, [(2, 1), (3, 2)], [1, 2, 3, 6, 9, 18]⟩,
    ⟨19, [(19, 1)], [1, 19]⟩,
    ⟨20, [(2, 2), (5, 1)], [1, 2, 4, 5, 10, 20]⟩,
    ⟨21, [(3, 1), (7, 1)], [1, 3, 7, 21]⟩,
    ⟨22, [(2, 1), (11, 1)], [1, 2, 11, 22]⟩,
    ⟨23, [(23, 1)], [1, 23]⟩,
    ⟨24, [(2, 3), (3, 1)], [1, 2, 3, 4, 6, 8, 12, 24]⟩,
    ⟨25, [(5, 2)], [1, 5, 25]⟩,
    ⟨26, [(2, 1), (13, 1)], [1, 2, 13, 26]⟩,
    ⟨27, [(3, 3)], [1, 3, 9, 27]⟩,
    ⟨28, [(2, 2), (7, 1)], [1, 2, 4, 7, 14, 28]⟩,
    ⟨29, [(29, 1)], [1, 29]⟩,
    ⟨30, [(2, 1), (3, 1), (5, 1)], [1, 2, 3, 5, 6, 10, 15, 30]⟩,
    ⟨31, [(31, 1)], [1, 31]⟩,
    ⟨32, [(2, 5)], [1, 2, 4, 8, 16, 32]⟩,
    ⟨33, [(3, 1), (11, 1)], [1, 3, 11, 33]⟩,
    ⟨34, [(2, 1), (17, 1)], [1, 2, 17, 34]⟩,
    ⟨35, [(5, 1), (7, 1)], [1, 5, 7, 35]⟩,
    ⟨36, [(2, 2), (3, 2)], [1, 2, 3, 4, 6, 9, 12, 18, 36]⟩,
    ⟨37, [(37, 1)], [1, 37]⟩,
    ⟨38, [(2, 1), (19, 1)], [1, 2, 19, 38]⟩,
    ⟨39, [(3, 1), (13, 1)], [1, 3, 13, 39]⟩,
    ⟨40, [(2, 3), (5, 1)], [1, 2, 4, 5, 8, 10, 20, 40]⟩,
    ⟨41, [(41, 1)], [1, 41]⟩,
    ⟨42, [(2, 1), (3, 1), (7, 1)], [1, 2, 3, 6, 7, 14, 21, 42]⟩,
    ⟨43, [(43, 1)], [1, 43]⟩,
    ⟨44, [(2, 2), (11, 1)], [1, 2, 4, 11, 22, 44]⟩,
    ⟨45, [(3, 2), (5, 1)], [1, 3, 5, 9, 15, 45]⟩,
    ⟨46, [(2, 1), (23, 1)], [1, 2, 23, 46]⟩,
    ⟨47, [(47, 1)], [1, 47]⟩,
    ⟨48, [(2, 4), (3, 1)], [1, 2, 3, 4, 6, 8, 12, 16, 24, 48]⟩,
    ⟨49, [(7, 2)], [1, 7, 49]⟩,
    ⟨50, [(2, 1), (5, 2)], [1, 2, 5, 10, 25, 50]⟩,
    ⟨51, [(3, 1), (17, 1)], [1, 3, 17, 51]⟩,
    ⟨52, [(2, 2), (13, 1)], [1, 2, 4, 13, 26, 52]⟩,
    ⟨53, [(53, 1)], [1, 53]⟩,
    ⟨54, [(2, 1), (3, 3)], [1, 2, 3, 6, 9, 18, 27, 54]⟩,
    ⟨55, [(5, 1), (11, 1)], [1, 5, 11, 55]⟩,
    ⟨56, [(2, 3), (7, 1)], [1, 2, 4, 7, 8, 14, 28, 56]⟩,
    ⟨57, [(3, 1), (19, 1)], [1, 3, 19, 57]⟩,
    ⟨58, [(2, 1), (29, 1)], [1, 2, 29, 58]⟩,
    ⟨59, [(59, 1)], [1, 59]⟩,
    ⟨60, [(2, 2), (3, 1), (5, 1)], [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60]⟩,
    ⟨61, [(61, 1)], [1, 61]⟩,
    ⟨62, [(2, 1), (31, 1)], [1, 2, 31, 62]⟩,
    ⟨63, [(3, 2), (7, 1)], [1, 3, 7, 9, 21, 63]⟩,
    ⟨64, [(2, 6)], [1, 2, 4, 8, 16, 32, 64]⟩
  ]

theorem chunk_checked : checkGoodBlock 4294967296 1 certificates = true := by decide +kernel

private theorem length_eq : certificates.length = 64 := by decide +kernel

theorem good_on_interval : ∀ n, 1 ≤ n → n < 65 → Good n := by
  intro n hn hlast
  apply checkGoodBlock_sound chunk_checked n hn
  simpa only [length_eq] using hlast

#print axioms chunk_checked
#print axioms good_on_interval

end D5.S3.Arith.ErdosNicolas.Data.Base00
