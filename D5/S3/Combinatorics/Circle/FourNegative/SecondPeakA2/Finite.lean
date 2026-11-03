/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Finite and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Small

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative

structure BoundaryRow where
  p : ℕ
  q : ℕ
  h : ℕ
  v : ℕ
  m : ℕ
  M : ℕ
  before : Bool
  deriving DecidableEq

def BoundaryRow.Check (r : BoundaryRow) : Prop :=
  1≤r.v ∧ 2*r.v≤4*r.p*r.q ∧ r.m<r.M ∧ 2*r.M<8*r.h*r.p*r.q ∧
    r.m &&& r.M=r.m ∧ Windows r.p r.q r.h r.v r.m r.M r.before

def boundaryRows : List BoundaryRow := [
  ⟨4,2,1,4,6,7,true⟩,
  ⟨4,2,2,5,10,14,false⟩,
  ⟨4,4,1,6,16,20,true⟩,
  ⟨4,4,2,6,32,40,true⟩,
  ⟨4,8,1,5,44,46,false⟩,
  ⟨4,8,2,4,90,91,true⟩,
  ⟨4,16,1,43,33,97,true⟩,
  ⟨4,16,2,24,129,193,false⟩,
  ⟨4,32,1,7,194,199,true⟩,
  ⟨4,32,2,7,388,398,true⟩,
  ⟨8,2,1,9,10,14,true⟩,
  ⟨8,2,2,12,9,27,true⟩,
  ⟨8,4,1,8,38,39,true⟩,
  ⟨8,4,2,8,76,78,true⟩,
  ⟨8,8,1,9,88,90,true⟩,
  ⟨8,8,2,9,176,180,true⟩,
  ⟨8,16,1,47,129,193,true⟩,
  ⟨8,16,2,87,129,385,false⟩,
  ⟨8,32,1,10,394,398,true⟩,
  ⟨8,32,2,13,778,795,true⟩,
  ⟨16,2,1,28,2,26,false⟩,
  ⟨16,2,2,28,4,52,false⟩,
  ⟨16,4,1,17,74,78,true⟩,
  ⟨16,4,2,18,146,155,false⟩,
  ⟨16,8,1,25,164,180,true⟩,
  ⟨16,8,2,25,328,360,true⟩,
  ⟨16,16,1,16,384,385,true⟩,
  ⟨16,16,2,16,768,769,true⟩,
  ⟨16,32,1,27,776,794,true⟩,
  ⟨16,32,2,27,1552,1588,true⟩,
  ⟨32,2,1,55,4,52,true⟩,
  ⟨32,2,2,55,8,104,true⟩,
  ⟨32,4,1,36,144,154,true⟩,
  ⟨32,4,2,36,288,308,true⟩,
  ⟨32,8,1,34,354,359,true⟩,
  ⟨32,8,2,34,708,718,true⟩,
  ⟨32,16,1,346,258,770,false⟩,
  ⟨32,16,2,189,1025,1537,true⟩,
  ⟨32,32,1,34,1584,1588,true⟩,
  ⟨32,32,2,34,3168,3176,true⟩]

private theorem boundary_checked : ∀ r∈boundaryRows, r.Check := by
  simp only [boundaryRows,List.mem_cons,List.mem_singleton]
  intro r hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem boundary_good (r : BoundaryRow) (hr : r∈boundaryRows) :
    Good r.p r.q r.h r.v r.m r.M r.before := by
  obtain ⟨hv,hv',hm,hM,hsub,hw⟩ := boundary_checked r hr
  exact ⟨hv,hv',hm,hM,SecondPeakHighD.submask_of_land r.m r.M hsub,hw⟩

/-- The genuine finite remainder is exhausted, with both fresh cuts retained. -/
theorem finite_exists (p q h : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32)
    (hq : q=2 ∨ q=4 ∨ q=8 ∨ q=16 ∨ q=32) (hh : h=1 ∨ h=2) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p q h v m M before := by
  rcases hp with rfl|rfl|rfl|rfl <;>
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> rcases hh with rfl|rfl
  · exact ⟨4,6,7,true,boundary_good ⟨4,2,1,4,6,7,true⟩ (by decide)⟩
  · exact ⟨5,10,14,false,boundary_good ⟨4,2,2,5,10,14,false⟩ (by decide)⟩
  · exact ⟨6,16,20,true,boundary_good ⟨4,4,1,6,16,20,true⟩ (by decide)⟩
  · exact ⟨6,32,40,true,boundary_good ⟨4,4,2,6,32,40,true⟩ (by decide)⟩
  · exact ⟨5,44,46,false,boundary_good ⟨4,8,1,5,44,46,false⟩ (by decide)⟩
  · exact ⟨4,90,91,true,boundary_good ⟨4,8,2,4,90,91,true⟩ (by decide)⟩
  · exact ⟨43,33,97,true,boundary_good ⟨4,16,1,43,33,97,true⟩ (by decide)⟩
  · exact ⟨24,129,193,false,boundary_good ⟨4,16,2,24,129,193,false⟩ (by decide)⟩
  · exact ⟨7,194,199,true,boundary_good ⟨4,32,1,7,194,199,true⟩ (by decide)⟩
  · exact ⟨7,388,398,true,boundary_good ⟨4,32,2,7,388,398,true⟩ (by decide)⟩
  · exact ⟨9,10,14,true,boundary_good ⟨8,2,1,9,10,14,true⟩ (by decide)⟩
  · exact ⟨12,9,27,true,boundary_good ⟨8,2,2,12,9,27,true⟩ (by decide)⟩
  · exact ⟨8,38,39,true,boundary_good ⟨8,4,1,8,38,39,true⟩ (by decide)⟩
  · exact ⟨8,76,78,true,boundary_good ⟨8,4,2,8,76,78,true⟩ (by decide)⟩
  · exact ⟨9,88,90,true,boundary_good ⟨8,8,1,9,88,90,true⟩ (by decide)⟩
  · exact ⟨9,176,180,true,boundary_good ⟨8,8,2,9,176,180,true⟩ (by decide)⟩
  · exact ⟨47,129,193,true,boundary_good ⟨8,16,1,47,129,193,true⟩ (by decide)⟩
  · exact ⟨87,129,385,false,boundary_good ⟨8,16,2,87,129,385,false⟩ (by decide)⟩
  · exact ⟨10,394,398,true,boundary_good ⟨8,32,1,10,394,398,true⟩ (by decide)⟩
  · exact ⟨13,778,795,true,boundary_good ⟨8,32,2,13,778,795,true⟩ (by decide)⟩
  · exact ⟨28,2,26,false,boundary_good ⟨16,2,1,28,2,26,false⟩ (by decide)⟩
  · exact ⟨28,4,52,false,boundary_good ⟨16,2,2,28,4,52,false⟩ (by decide)⟩
  · exact ⟨17,74,78,true,boundary_good ⟨16,4,1,17,74,78,true⟩ (by decide)⟩
  · exact ⟨18,146,155,false,boundary_good ⟨16,4,2,18,146,155,false⟩ (by decide)⟩
  · exact ⟨25,164,180,true,boundary_good ⟨16,8,1,25,164,180,true⟩ (by decide)⟩
  · exact ⟨25,328,360,true,boundary_good ⟨16,8,2,25,328,360,true⟩ (by decide)⟩
  · exact ⟨16,384,385,true,boundary_good ⟨16,16,1,16,384,385,true⟩ (by decide)⟩
  · exact ⟨16,768,769,true,boundary_good ⟨16,16,2,16,768,769,true⟩ (by decide)⟩
  · exact ⟨27,776,794,true,boundary_good ⟨16,32,1,27,776,794,true⟩ (by decide)⟩
  · exact ⟨27,1552,1588,true,boundary_good ⟨16,32,2,27,1552,1588,true⟩ (by decide)⟩
  · exact ⟨55,4,52,true,boundary_good ⟨32,2,1,55,4,52,true⟩ (by decide)⟩
  · exact ⟨55,8,104,true,boundary_good ⟨32,2,2,55,8,104,true⟩ (by decide)⟩
  · exact ⟨36,144,154,true,boundary_good ⟨32,4,1,36,144,154,true⟩ (by decide)⟩
  · exact ⟨36,288,308,true,boundary_good ⟨32,4,2,36,288,308,true⟩ (by decide)⟩
  · exact ⟨34,354,359,true,boundary_good ⟨32,8,1,34,354,359,true⟩ (by decide)⟩
  · exact ⟨34,708,718,true,boundary_good ⟨32,8,2,34,708,718,true⟩ (by decide)⟩
  · exact ⟨346,258,770,false,boundary_good ⟨32,16,1,346,258,770,false⟩ (by decide)⟩
  · exact ⟨189,1025,1537,true,boundary_good ⟨32,16,2,189,1025,1537,true⟩ (by decide)⟩
  · exact ⟨34,1584,1588,true,boundary_good ⟨32,32,1,34,1584,1588,true⟩ (by decide)⟩
  · exact ⟨34,3168,3176,true,boundary_good ⟨32,32,2,34,3168,3176,true⟩ (by decide)⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
