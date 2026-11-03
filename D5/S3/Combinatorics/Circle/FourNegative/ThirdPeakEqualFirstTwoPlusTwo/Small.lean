import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Physical

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open SourceWidth
open private banks from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Banks
open private oldValue newValue sourceMod base
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

-- The transferred occurrence is the original V bit 0, physical label 4.
private theorem d4_banks :
    banks 2 2 6 4 1 11 0=[1,2] ∧ banks 2 2 6 4 1 11 1=[10] ∧
    banks 2 2 6 4 1 11 2=[12,4,5,7] ∧ banks 2 2 6 4 1 11 3=[0,6,8] := by
  decide

private theorem transfer_algebra (f : ℕ→ℤ) :
    (([1,2,9,10,4,11].map f).sum)=(([1,2,9,10,11].map f).sum)+f 4 ∧
    (([1,2,9,10,4,11,12,5,7,13].map f).sum)=
      (([1,2,9,10,11,12,4,5,7,13].map f).sum) := by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  constructor <;> ring

private theorem d4_transfer_values :
    oldValue 2 2 6 4 4=337 ∧ newValue 2 2 6 4 4=673 ∧
    2*(([1,2,9,10,4,11].map (oldValue 2 2 6 4)).sum)-
      2*(([1,2,9,10,11].map (oldValue 2 2 6 4)).sum)=2*337 ∧
    2*(([1,2,9,10,4,11].map (newValue 2 2 6 4)).sum)-
      2*(([1,2,9,10,11].map (newValue 2 2 6 4)).sum)=2*673 := by
  have ho:=transfer_algebra (oldValue 2 2 6 4)
  have hn:=transfer_algebra (newValue 2 2 6 4)
  have hvo : oldValue 2 2 6 4 4=337 := by norm_num [oldValue,sourceMod,base,centered]
  have hvn : newValue 2 2 6 4 4=673 := by norm_num [newValue,sourceMod,base,centered]
  exact ⟨hvo,hvn,by linarith only [ho.1,hvo],by linarith only [hn.1,hvn]⟩

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
