/- GID: D5/S3/Combinatorics/PopStack/PopStackThirdBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackThirdBijection
   mirror-E: none(waiver:recursive-minimum-third-construction)
   anchors: []
   utility: none
   digest: Recursive five-case minimum-third replacement and its proposed inverse operations. -/

import D5.S3.Combinatorics.PopStack.PopStackThirdDecomposition
import D5.S3.Combinatorics.PopStack.PopStackMinimumBijection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackThirdBijection

open PopStackDefs PopStackInflation PopStackFamilies PopStackM3Disjoint
open PopStackTerminalGap PopStackTerminalIntervals

noncomputable section

open Classical in
mutual
  def Phi : ℕ → List ℕ → List ℕ
    | 0, _ => []
    | size + 1, member =>
      if size + 1 = 4 then [2, 4, 1, 3]
      else
        let predecessor := (member.eraseIdx 1).map Nat.pred
        if IsSimple predecessor then
          if predecessor.getD 2 0 = 1 then
            2 :: (undoPhi size predecessor).map
              (fun entry => if entry = 1 then 1 else entry + 1)
          else (predecessor.map Nat.succ).insertIdx 2 1
        else if predecessor = B size then Y (size + 1)
        else
          let skeleton := deflateFirst predecessor
          if skeleton.getD 1 0 = 1 then
            2 :: (inflate skeleton 1 [1, 2]).map
              (fun entry => if entry = 1 then 1 else entry + 1)
          else ((inflate skeleton 1 [2, 1]).map Nat.succ).insertIdx 2 1

  def undoPhi : ℕ → List ℕ → List ℕ
    | 0, _ => []
    | size + 1, member =>
      if size + 1 = 4 then [3, 1, 4, 2]
      else if member.getD 0 0 = 2 then
        let parent := (member.drop 1).map
          (fun entry => if entry = 1 then 1 else entry - 1)
        if IsSimple parent then ((Phi size parent).map Nat.succ).insertIdx 1 1
        else
          let skeleton := (parent.eraseIdx 2).map
            (fun entry => if entry = 1 then 1 else entry - 1)
          ((inflate skeleton 0 [2, 1]).map Nat.succ).insertIdx 1 1
      else
        let predecessor := (member.eraseIdx 2).map Nat.pred
        if IsSimple predecessor then (predecessor.map Nat.succ).insertIdx 1 1
        else if predecessor = R size then ((B size).map Nat.succ).insertIdx 1 1
        else
          let pivot := predecessor.getD 2 0
          let skeleton := (predecessor.eraseIdx 1).map
            (fun entry => if pivot < entry then entry - 1 else entry)
          ((inflate skeleton 0 [2, 1]).map Nat.succ).insertIdx 1 1
end

end

end D5.S3.Combinatorics.PopStack.PopStackThirdBijection
