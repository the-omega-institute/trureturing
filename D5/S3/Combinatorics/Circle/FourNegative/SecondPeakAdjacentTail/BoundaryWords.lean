/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/BoundaryWords
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/BoundaryWords
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Three literal exceptional physical words and paired strips. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open SourceWidth
open private oldValue newValue sourceMod base
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

/-- The three exact physical exceptions. Their sources retain the original seed. -/
private def boundaryWord : Fin 3 → List ℕ :=
  ![[0,1,2,3,4,5,7,6,8,10,11,9,12,13],
    [0,1,2,3,4,5,6,7,8,9,11,10,12,13,14,16,17,15,18,19],
    [0,1,2,3,4,5,7,8,6,9,11,12,10,13,14]]
private def boundaryB : Fin 3 → ℕ := ![5,7,6]
private def boundaryC : Fin 3 → ℕ := ![3,5,3]
private def boundaryCut : Fin 3 → ℕ := ![13,19,14]

/-- Finite kernel arithmetic evidence only; no decision procedure on an infinite order. -/
private theorem boundary_strips (r : Fin 3) :
    let b := boundaryB r
    let c := boundaryC r
    let k := 2+b+c+(c+1)
    let w := boundaryWord r
    w.Perm (List.range k) ∧ boundaryCut r≤k ∧
    InStrip (oldValue 2 b c (c+1)) (sourceMod 2 b c (c+1)/2) 0 w ∧
    InStrip (newValue 2 b c (c+1)) (sourceMod 2 b c (c+1)) 0
      (insertAt k w (boundaryCut r)) := by
  fin_cases r
  all_goals dsimp [boundaryB,boundaryC,boundaryWord,boundaryCut]
  all_goals refine ⟨by decide,by decide,?_,?_⟩
  all_goals norm_num [InStrip,oldValue,newValue,sourceMod,base,centered,insertAt]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
