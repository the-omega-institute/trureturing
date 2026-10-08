/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Endpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Endpoints
   mirror-E: none(waiver:finite-signed-walk-endpoints)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: none
   digest: Weighted endpoint propagation counts signed walks and bounds their terminal labels. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftSigned
import D5.S3.Combinatorics.InversionSeq.InversionSeq207RightReduction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Endpoints

open InversionSeq207LeftSigned InversionSeq207RightReduction

noncomputable def walkStep (isLeft : Bool) (label : ℕ × ℕ) : (ℕ × ℕ) →₀ ℤ :=
  if isLeft then
    (∑ index ∈ Finset.range label.2, Finsupp.single (label.1 + 1, index) 1) +
      (∑ distance ∈ Finset.range (label.1 + 1),
        Finsupp.single (label.1 - distance, label.2 + distance) 1) +
      Finsupp.single (label.1 + 1, 0) 1 - Finsupp.single (0, 0) 1
  else
    Finsupp.single (label.1 + 1, 0) (1 - (label.2 : ℤ)) +
      Finsupp.single (label.1, 0) (label.2 : ℤ) +
      (∑ distance ∈ Finset.range label.1,
        Finsupp.single (label.1 - distance, distance + 1) 1) +
      ∑ distance ∈ Finset.range label.2, Finsupp.single (label.1 + 1, distance + 1) 1

noncomputable def walkEndpoints (isLeft : Bool) : ℕ → (ℕ × ℕ) →₀ ℤ
  | 0 => Finsupp.single (0, 0) 1
  | depth + 1 => Finsupp.linearCombination ℤ (walkStep isLeft) (walkEndpoints isLeft depth)


end D5.S3.Combinatorics.InversionSeq.InversionSeq207Endpoints
