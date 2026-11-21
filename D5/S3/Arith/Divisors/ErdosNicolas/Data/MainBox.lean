/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/MainBox
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/MainBox.main_box_ok
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main03
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main04
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main05
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main06
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main07
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main08
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main09
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main10
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main11
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main12
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main13
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main14
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main15
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main16
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main17
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main18
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main19
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main20
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main21
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Main22

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.MainBox

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

private def n1005 : MainTree := .split 2 1 Main02.certificate Main03.certificate

private theorem c1005 : C ![2, 2, 0, 0, 0, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n1005 := by
  exact checkExponentBoxTree_join Main02.chunk_checked Main03.chunk_checked (by decide +kernel)

private def n633 : MainTree := .split 0 1 Main01.certificate n1005

private theorem c633 : C ![0, 2, 0, 0, 0, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n633 := by
  exact checkExponentBoxTree_join Main01.chunk_checked c1005 (by decide +kernel)

private def n1 : MainTree := .split 1 1 Main00.certificate n633

private theorem c1 : C ![0, 0, 0, 0, 0, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n1 := by
  exact checkExponentBoxTree_join Main00.chunk_checked c633 (by decide +kernel)

private def n1801 : MainTree := .split 2 1 Main04.certificate Main05.certificate

private theorem c1801 : C ![4, 0, 0, 0, 0, 0, 0] ![17, 1, 3, 2, 1, 1, 1] n1801 := by
  exact checkExponentBoxTree_join Main04.chunk_checked Main05.chunk_checked (by decide +kernel)

private def n2622 : MainTree := .split 1 3 Main07.certificate Main08.certificate

private theorem c2622 : C ![4, 2, 0, 1, 0, 0, 0] ![8, 7, 1, 2, 1, 1, 1] n2622 := by
  exact checkExponentBoxTree_join Main07.chunk_checked Main08.chunk_checked (by decide +kernel)

private def n2424 : MainTree := .split 3 0 Main06.certificate n2622

private theorem c2424 : C ![4, 2, 0, 0, 0, 0, 0] ![8, 7, 1, 2, 1, 1, 1] n2424 := by
  exact checkExponentBoxTree_join Main06.chunk_checked c2622 (by decide +kernel)

private def n3097 : MainTree := .split 2 0 Main11.certificate Main12.certificate

private theorem c3097 : C ![9, 4, 0, 1, 0, 0, 0] ![17, 7, 1, 2, 1, 1, 1] n3097 := by
  exact checkExponentBoxTree_join Main11.chunk_checked Main12.chunk_checked (by decide +kernel)

private def n3035 : MainTree := .split 1 3 Main10.certificate n3097

private theorem c3035 : C ![9, 2, 0, 1, 0, 0, 0] ![17, 7, 1, 2, 1, 1, 1] n3035 := by
  exact checkExponentBoxTree_join Main10.chunk_checked c3097 (by decide +kernel)

private def n2981 : MainTree := .split 3 0 Main09.certificate n3035

private theorem c2981 : C ![9, 2, 0, 0, 0, 0, 0] ![17, 7, 1, 2, 1, 1, 1] n2981 := by
  exact checkExponentBoxTree_join Main09.chunk_checked c3035 (by decide +kernel)

private def n2423 : MainTree := .split 0 8 n2424 n2981

private theorem c2423 : C ![4, 2, 0, 0, 0, 0, 0] ![17, 7, 1, 2, 1, 1, 1] n2423 := by
  exact checkExponentBoxTree_join c2424 c2981 (by decide +kernel)

private def n3439 : MainTree := .split 5 0 Main16.certificate Main17.certificate

private theorem c3439 : C ![4, 4, 2, 1, 1, 0, 0] ![8, 7, 3, 2, 1, 1, 1] n3439 := by
  exact checkExponentBoxTree_join Main16.chunk_checked Main17.chunk_checked (by decide +kernel)

private def n3395 : MainTree := .split 4 0 Main15.certificate n3439

private theorem c3395 : C ![4, 4, 2, 1, 0, 0, 0] ![8, 7, 3, 2, 1, 1, 1] n3395 := by
  exact checkExponentBoxTree_join Main15.chunk_checked c3439 (by decide +kernel)

private def n3249 : MainTree := .split 1 3 Main14.certificate n3395

private theorem c3249 : C ![4, 2, 2, 1, 0, 0, 0] ![8, 7, 3, 2, 1, 1, 1] n3249 := by
  exact checkExponentBoxTree_join Main14.chunk_checked c3395 (by decide +kernel)

private def n3129 : MainTree := .split 3 0 Main13.certificate n3249

private theorem c3129 : C ![4, 2, 2, 0, 0, 0, 0] ![8, 7, 3, 2, 1, 1, 1] n3129 := by
  exact checkExponentBoxTree_join Main13.chunk_checked c3249 (by decide +kernel)

private def n3540 : MainTree := .split 5 0 Main21.certificate Main22.certificate

private theorem c3540 : C ![9, 4, 2, 1, 1, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n3540 := by
  exact checkExponentBoxTree_join Main21.chunk_checked Main22.chunk_checked (by decide +kernel)

private def n3532 : MainTree := .split 4 0 Main20.certificate n3540

private theorem c3532 : C ![9, 4, 2, 1, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n3532 := by
  exact checkExponentBoxTree_join Main20.chunk_checked c3540 (by decide +kernel)

private def n3498 : MainTree := .split 1 3 Main19.certificate n3532

private theorem c3498 : C ![9, 2, 2, 1, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n3498 := by
  exact checkExponentBoxTree_join Main19.chunk_checked c3532 (by decide +kernel)

private def n3470 : MainTree := .split 3 0 Main18.certificate n3498

private theorem c3470 : C ![9, 2, 2, 0, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n3470 := by
  exact checkExponentBoxTree_join Main18.chunk_checked c3498 (by decide +kernel)

private def n3128 : MainTree := .split 0 8 n3129 n3470

private theorem c3128 : C ![4, 2, 2, 0, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n3128 := by
  exact checkExponentBoxTree_join c3129 c3470 (by decide +kernel)

private def n2422 : MainTree := .split 2 1 n2423 n3128

private theorem c2422 : C ![4, 2, 0, 0, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n2422 := by
  exact checkExponentBoxTree_join c2423 c3128 (by decide +kernel)

private def n1800 : MainTree := .split 1 1 n1801 n2422

private theorem c1800 : C ![4, 0, 0, 0, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n1800 := by
  exact checkExponentBoxTree_join c1801 c2422 (by decide +kernel)

private def n0 : MainTree := .split 0 3 n1 n1800

private theorem c0 : C ![0, 0, 0, 0, 0, 0, 0] ![17, 7, 3, 2, 1, 1, 1] n0 := by
  exact checkExponentBoxTree_join c1 c1800 (by decide +kernel)

/-- Full certificate for all 13824 main-box exponent vectors. -/
def certificate : MainTree := n0

private theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes (fun _ => 0) mainCaps certificate = true :=
  checkExponentBoxTree_bounds_congr c0 (by decide +kernel) (by decide +kernel)

/-- The checked main certificate has exactly the finite scope required by classification. -/
theorem main_box_ok (hbase : BaseOK) : MainBoxOK :=
  mainBoxOK_of_checked_tree certificate hbase chunk_checked

#print axioms chunk_checked
#print axioms main_box_ok

end D5.S3.Arith.ErdosNicolas.Data.MainBox
