/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Main
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/Main
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: none
   digest: The unconditional Erdos-Nicolas theorem from six kernel-checked finite certificates. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.Base
import D5.S3.Arith.Divisors.ErdosNicolas.Data.SmallLifts
import D5.S3.Arith.Divisors.ErdosNicolas.Data.LargeLifts
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueTrees
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainBox
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Extra

/-! All finite premises of the strong induction are supplied by checked certificate data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

/-- Every integer above the last exception has reciprocal divisor gap sum below its count. -/
theorem erdos_nicolas : ∀ n : ℕ, 5040 < n → hHat n < (n.divisors.card : ℚ) :=
  erdos_nicolas_of_finite_certificates Data.Base.base_ok
    (Data.SmallLifts.small_ok Data.Base.base_ok) Data.LargeLifts.large_ok
    Data.ResidueTrees.residue_tree_ok (Data.MainBox.main_box_ok Data.Base.base_ok)
    Data.Extra.extra_ok

#print axioms erdos_nicolas

end D5.S3.Arith.ErdosNicolas
