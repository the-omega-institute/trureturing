import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Physical

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open SourceWidth
open private banks from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Banks
open private oldValue newValue sourceMod base
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

-- Three ground proofs evaluate the defining centered modular source and literal words.
-- The d=4 word retains total V mask 11 and its actual cut is 9.
private theorem small_cases (d : ℕ) (hd : d=4 ∨ d=5 ∨ d=6) :
    ∃ pre tail : List ℕ,
      (pre++(2*2+2*d+2-1)::tail).Perm (List.range (2*2+2*d+2)) ∧
      InStrip (oldValue 2 2 (d+2) d) (sourceMod 2 2 (d+2) d/2) 0
        (pre++(2*2+2*d+2-1)::tail) ∧
      InStrip (newValue 2 2 (d+2) d) (sourceMod 2 2 (d+2) d) 0
        (pre++(2*2+2*d+2)::(2*2+2*d+2-1)::tail) := by
  rcases hd with rfl|rfl|rfl
  · refine ⟨[1,2,9,10,4,11,12,5,7],[0,6,8,3],?_,?_,?_⟩
    · decide
    · norm_num [InStrip,oldValue,sourceMod,base,centered]
    · norm_num [InStrip,newValue,sourceMod,base,centered]
  · refine ⟨[0,1,2,3,11,12,13,14,5,6,7,8],[9,10,4],?_,?_,?_⟩
    · decide
    · norm_num [InStrip,oldValue,sourceMod,base,centered]
    · norm_num [InStrip,newValue,sourceMod,base,centered]
  · refine ⟨[0,1,3,4,13,14,15,16,6,7,9,11],[2,8,10,12,5],?_,?_,?_⟩
    · decide
    · norm_num [InStrip,oldValue,sourceMod,base,centered]
    · norm_num [InStrip,newValue,sourceMod,base,centered]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
