/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding
   mirror-E: none(waiver:filtered-value-partition-and-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Filtered values give the block allocation, reconstruction, and extraction algorithms. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWords
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWordEncoding

open FishburnTenSevenWords FishburnTenSevenWords.Letter

def blocks {size : ℕ} (word : Fin size → Letter) : List ℕ × List ℕ × List ℕ :=
  let select (letter : Letter) :=
    ((List.finRange size).filter (fun index => decide (word index = letter))).map
      (fun index => index.val + 2)
  ((select d).reverse, select i, (select j).reverse)

def encodeBlocks {size : ℕ} (parts : List ℕ × List ℕ × List ℕ) : Fin size → Letter :=
  fun index => if index.val + 2 ∈ parts.1 then d
    else if index.val + 2 ∈ parts.2.1 then i else j

def reconstruct {size : ℕ} (total : ℕ) (word : Fin size → Letter) : List ℕ :=
  let parts := blocks word
  (List.range' (size + 3) (total - (size + 2))).reverse ++ parts.1 ++
    1 :: (parts.2.1 ++ (size + 2) :: parts.2.2)

def encodePermutation {size : ℕ} (permutation : List ℕ) : Fin size → Letter :=
  fun index => if index.val + 2 ∈ permutation.takeWhile (fun value => value != 1) then d
    else if index.val + 2 ∈
      (permutation.dropWhile (fun value => value != 1)).tail.takeWhile
        (fun value => value != size + 2) then i else j


end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWordEncoding
