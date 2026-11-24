/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group05
   generality: I
   mirror-B: none(waiver:finite-coverage-helper-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificates)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0400.checked0400
   digest: Adjacent checker successes cover a complete interval of odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0400
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0401
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0402
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0403
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0404
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0405
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0406
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0407
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0408
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0409
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0410
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0411
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0412
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0413
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0414
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0415
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0417
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0418
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0419
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0420
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0421
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0422
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0423
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0424
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0425

set_option maxRecDepth 10000

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

attribute [local irreducible] checkBlock checkRows checkPrime

private theorem checkedGroup05 :
    checkBlock 3276803 103340 (
      rows0400 ++
      rows0401 ++
      rows0402 ++
      rows0403 ++
      rows0404 ++
      rows0405 ++
      rows0406 ++
      rows0407 ++
      rows0408 ++
      rows0409 ++
      rows0410 ++
      rows0411 ++
      rows0412 ++
      rows0413 ++
      rows0414 ++
      rows0415 ++
      rows0416 ++
      rows0417 ++
      rows0418 ++
      rows0419 ++
      rows0420 ++
      rows0421 ++
      rows0422 ++
      rows0423 ++
      rows0424 ++
      rows0425) = true := by
  exact checkBlock_append checked0400 (
    checkBlock_append checked0401 (
    checkBlock_append checked0402 (
    checkBlock_append checked0403 (
    checkBlock_append checked0404 (
    checkBlock_append checked0405 (
    checkBlock_append checked0406 (
    checkBlock_append checked0407 (
    checkBlock_append checked0408 (
    checkBlock_append checked0409 (
    checkBlock_append checked0410 (
    checkBlock_append checked0411 (
    checkBlock_append checked0412 (
    checkBlock_append checked0413 (
    checkBlock_append checked0414 (
    checkBlock_append checked0415 (
    checkBlock_append checked0416 (
    checkBlock_append checked0417 (
    checkBlock_append checked0418 (
    checkBlock_append checked0419 (
    checkBlock_append checked0420 (
    checkBlock_append checked0421 (
    checkBlock_append checked0422 (
    checkBlock_append checked0423 (
    checkBlock_append checked0424 (
    checked0425)))))))))))))))))))))))))

/-- Complete prime-root coverage of this consecutive group of checked odd slots. -/
theorem group05_sound :
    ∀ k, k < 103340 → (3276803 + 2 * k).Prime →
      ∃ q, q.Prime ∧ q < 3276803 + 2 * k ∧
        orderOf (q : ZMod (3276803 + 2 * k)) = 3276803 + 2 * k - 1 :=
  checkBlock_sound checkedGroup05

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
