/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Base
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Base.base_ok
   digest: The entire positive base interval from checked integer blocks. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base03
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base04
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base05
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base06
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base07
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base08
import D5.S3.Arith.Divisors.ErdosNicolas.Classification

/-! Exact assembly of the consecutive base intervals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas.Data.Base

open D5.S3.Arith.ErdosNicolas

theorem base_ok : BaseOK := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  by_cases h0 : n < 65
  · exact Base00.good_on_interval n (by omega) h0
  by_cases h1 : n < 820
  · exact Base01.good_on_interval n (by omega) h1
  by_cases h2 : n < 1534
  · exact Base02.good_on_interval n (by omega) h2
  by_cases h3 : n < 2227
  · exact Base03.good_on_interval n (by omega) h3
  by_cases h4 : n < 2914
  · exact Base04.good_on_interval n (by omega) h4
  by_cases h5 : n < 3586
  · exact Base05.good_on_interval n (by omega) h5
  by_cases h6 : n < 4259
  · exact Base06.good_on_interval n (by omega) h6
  by_cases h7 : n < 4920
  · exact Base07.good_on_interval n (by omega) h7
  exact Base08.good_on_interval n (by omega) (by omega)

#print axioms base_ok

end D5.S3.Arith.ErdosNicolas.Data.Base
