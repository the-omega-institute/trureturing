/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/MainSupport
   generality: I
   mirror-B: none(waiver:certificate-payload-without-standalone-claim)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: none
   digest: Generated divisor tables and exact leaf formats for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.BoxChecker
import D5.S3.Arith.Divisors.ErdosNicolas.FactorDivisors

/-! Only compact exponent vectors are stored; the reflected checker verifies all generated lists. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.ErdosNicolas.Data

/-- The fixed integer scale of the main finite certificate. -/
def mainScale : ℕ := 4294967296

/-- Main-box trees have exactly the seven prime coordinates. -/
abbrev MainTree := ExponentBoxTree 7

/-- Fuel makes both recursive branches kernel-computable without well-founded unfolding. -/
private def certificateMerge : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | f + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: certificateMerge f xs (y :: ys)
    else y :: certificateMerge f (x :: xs) ys

private def certificateSort : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | f + 1, x :: y :: xs =>
    let ds := x :: y :: xs
    let mid := ds.length / 2
    let left := certificateSort f (ds.take mid)
    let right := certificateSort f (ds.drop mid)
    certificateMerge (left.length + right.length) left right

/-- Fuel-bounded sorting is independently verified by each complete-table check. -/
def certificateDivisors (fs : List (ℕ × ℕ)) : List ℕ :=
  let raw := factorDivisors fs
  certificateSort raw.length raw

private def unpackIndexBlock (base : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, block => block % base :: unpackIndexBlock base k (block / base)

private def indexedFactorDivisor : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 1
  | (p, _) :: fs, i =>
    p ^ (i / factorTau fs) * indexedFactorDivisor fs (i % factorTau fs)

/-- Packed mixed-radix indices avoid sorting and avoid random access into long lists. -/
def certificateIndexedDivisors (fs : List (ℕ × ℕ)) (base blockSize count : ℕ)
    (blocks : List ℕ) : List ℕ :=
  ((blocks.flatMap (unpackIndexBlock base blockSize)).take count).map
    (indexedFactorDivisor fs)

/-- An untrusted balanced directory of packed blocks; readouts are checked pointwise. -/
inductive PackedIndexTree where
  | leaf (block : ℕ)
  | node (leftCount : ℕ) (left right : PackedIndexTree)

private def readPackedBlock : PackedIndexTree → ℕ → ℕ
  | .leaf n, _ => n
  | .node count left right, i =>
    if i < count then readPackedBlock left i else readPackedBlock right (i - count)

/-- Read one divisor in logarithmic directory depth, without traversing the divisor list. -/
def indexedPackedReadout (fs : List (ℕ × ℕ)) (base blockSize : ℕ)
    (tree : PackedIndexTree) (i : ℕ) : ℕ :=
  indexedFactorDivisor fs
    ((readPackedBlock tree (i / blockSize) / base ^ (i % blockSize)) % base)

/-- Complete generated upper-corner divisor list. -/
def mainDivisors (hi : Fin 7 → ℕ) : List ℕ :=
  certificateDivisors (exponentFactors boxPrimes hi)

/-- A gap leaf may use either compact divisor generator; both are checked independently. -/
def mainGapLeafOfDivisors (hi : Fin 7 → ℕ) (ds : List ℕ) : ExponentBoxLeaf :=
  let t := factorTau (exponentFactors boxPrimes hi)
  .gap ds (computeGapPrefixes mainScale t) (computeGapWeights mainScale t)

/-- A linear adjacent-gap leaf with generated prefixes and weights. -/
def mainGapLeaf (hi : Fin 7 → ℕ) : ExponentBoxLeaf :=
  let t := factorTau (exponentFactors boxPrimes hi)
  .gap (mainDivisors hi) (computeGapPrefixes mainScale t) (computeGapWeights mainScale t)

/-- A complete rank-partition leaf, with either of the two specified rank parameters. -/
def mainRankLeaf (R : ℕ) (hi : Fin 7 → ℕ) : ExponentBoxLeaf :=
  .rank R (mainDivisors hi)

/-- A singleton leaf checked by the complete pair upper and exceptional lower sums. -/
def mainFullLeaf (hi : Fin 7 → ℕ) : ExponentBoxLeaf := .full (mainDivisors hi)

end D5.S3.Arith.ErdosNicolas.Data
