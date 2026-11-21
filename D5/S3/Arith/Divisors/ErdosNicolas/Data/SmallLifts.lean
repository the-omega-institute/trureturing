/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/SmallLifts
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/SmallLifts.small_ok
   digest: Exact coverage of all small lifts using checked blocks and the base theorem. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.Small00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Small01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Small02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Small03
import D5.S3.Arith.Divisors.ErdosNicolas.Classification

/-! The lower base range is reused rather than computing its full pair sums again. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas.Data.SmallLifts

open D5.S3.Arith.ErdosNicolas

private def allCertificates : List NumberCertificate :=
  Small00.certificates ++ Small01.certificates ++ Small02.certificates ++ Small03.certificates

private theorem all_checked : allCertificates.all (checkGood 4294967296) = true := by
  simp only [allCertificates, List.all_append, Small00.chunk_checked, Small01.chunk_checked,
    Small02.chunk_checked, Small03.chunk_checked, Bool.and_self]

private theorem coverage :
    ∀ n ∈ smallLifts,
      n ∈ certifiedValues allCertificates ∨ (1 ≤ n ∧ n ≤ 5040) := by decide +kernel

theorem small_ok (hbase : BaseOK) : SmallLiftsOK := by
  intro n hn
  rcases coverage n hn with hc | hb
  · exact good_of_mem_certifiedValues all_checked hc
  · exact hbase n (Finset.mem_Icc.mpr hb)

#print axioms small_ok

end D5.S3.Arith.ErdosNicolas.Data.SmallLifts
