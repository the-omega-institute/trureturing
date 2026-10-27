/- SOURCE DRAFT: exact actual-source legality and physical permutation control.
   No native_decide, axiom, sorry, or evaluation of enormous energy powers. -/
import D5.S3.Combinatorics.Circle.FreshNegativeSmallHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.Circle
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
example :
    let t := 3347513596725618
    let W : List (Fin 53) := [12,15,3,27,14,49,33,21]
    let V : List (Fin 53) := [12,15,3,1,26,14,49,33,21]
    Legal 53 t W ∧ Legal 53 t V ∧
    (V ++ [27]).Perm (W ++ [1,26]) ∧
    (finRotate 53).symm (27 : Fin 53) = 26 ∧
    s 53 t (1 : Fin 53) = -2312172061289755 ∧
    s 53 t (26 : Fin 53) = -1335744333573768 ∧
    s 53 t (27 : Fin 53) = -2671488667147536 ∧
    mass (s 53 t) W = 1228057543835872 ∧
    mass (s 53 t) V = 251629816119885 ∧
    mass (s 53 t) (W ++ [26]) < 0 := by
  dsimp only
  refine ⟨legal_of_strip (by decide) ?_, legal_of_strip (by decide) ?_,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  · change InStrip (s 53 3347513596725618) (C 53) 0
      ([12,15,3,27,14,49,33,21] : List (Fin 53))
    dsimp only [InStrip]
    decide
  · change InStrip (s 53 3347513596725618) (C 53) 0
      ([12,15,3,1,26,14,49,33,21] : List (Fin 53))
    dsimp only [InStrip]
    decide
