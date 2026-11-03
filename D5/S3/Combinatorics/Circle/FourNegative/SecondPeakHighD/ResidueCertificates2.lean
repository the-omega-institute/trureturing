/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/ResidueCertificates2
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Sixteen exact universal physical window and stock inequalities per residue row. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.TableData

/-! Exact HighD construction on unrestricted natural exponents. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

theorem residue_bounds_8 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 0) = 42467328*R^2 + 35338752*R + 7317296 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 35338752*R + 7317296 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+32) 2 0-1-(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+32) 2 0-1-(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 0)) = 297271296*R^2 + 267240960*R + 60053776 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤297271296*R^2 + 267240960*R + 60053776 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 0) = 169869312*R^2 + 146267136*R + 31452688 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 146267136*R + 31452688 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+32) 2 0-1-(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+32) 2 0-1-(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 0)) = 169869312*R^2 + 156312576*R + 35918384 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 156312576*R + 35918384 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 1) = 901251072*R^2 + 801228800*R + 178076640 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤901251072*R^2 + 801228800*R + 178076640 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+32) 2 1-1-(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+32) 2 1-1-(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 1)) = 457703424*R^2 + 406896640*R + 90432544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤457703424*R^2 + 406896640*R + 90432544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 1) = 1877999616*R^2 + 1669781504*R + 371162080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1877999616*R^2 + 1669781504*R + 371162080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+32) 2 1-1-(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+32) 2 1-1-(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 1)) = 839909376*R^2 + 746469376*R + 165856288 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤839909376*R^2 + 746469376*R + 165856288 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 2) = 2526806016*R^2 + 2246372352*R + 499265536 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2526806016*R^2 + 2246372352*R + 499265536 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+32) 2 2-1-(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+32) 2 2-1-(oldEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) 2)) = 97844723712*R^3 + 127975292928*R^2 + 55773508608*R + 8099090432 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 127975292928*R^2 + 55773508608*R + 8099090432 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 2) = 5053612032*R^2 + 4492753920*R + 998535168 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 4492753920*R + 998535168 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+32) 2 2-1-(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+32) 2 2-1-(newEnds 8 4 (72*R+32) 2 (4*(72*R+32)-2) 6 (1024*R+446) true 2)) = 195689447424*R^3 + 255908118528*R^2 + 111509185536*R + 16189755392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 255908118528*R^2 + 111509185536*R + 16189755392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+32)-2-1 := by
    have expansion : 8*(4*(72*R+32)-2-1) = 2304*R + 1000 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 1000 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+32)-2*(4*(72*R+32)-2) := by
    have expansion : 4*(T 8 4 (72*R+32)-2*(4*(72*R+32)-2)) = 6912*R + 3088 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 3088 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+446 := by
    have expansion : 8*(1024*R+446) = 8192*R + 3568 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 3568 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+32) 2-2-2*(1024*R+446) := by
    have expansion : 4*(Y 8 4 (72*R+32) 2-2-2*(1024*R+446)) = 28672*R + 12808 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 12808 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_8 (R : ℕ) : Submask 6 (1024*R+446) := by
  exact submask_high_block 10 R 446 6 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_9 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 0) = 42467328*R^2 + 73087488*R + 31412016 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 73087488*R + 31412016 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+64) 2 0-1-(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+64) 2 0-1-(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 0)) = 297271296*R^2 + 531482112*R + 237547792 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤297271296*R^2 + 531482112*R + 237547792 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 0) = 169869312*R^2 + 297262080*R + 130014736 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 297262080*R + 130014736 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+64) 2 0-1-(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+64) 2 0-1-(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 0)) = 169869312*R^2 + 307307520*R + 138945072 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 307307520*R + 138945072 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 1) = 1071120384*R^2 + 1904338944*R + 846428256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1071120384*R^2 + 1904338944*R + 846428256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+64) 2 1-1-(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+64) 2 1-1-(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 1)) = 287834112*R^2 + 511746048*R + 227461024 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤287834112*R^2 + 511746048*R + 227461024 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 1) = 2217738240*R^2 + 3943102464*R + 1752692832 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2217738240*R^2 + 3943102464*R + 1752692832 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+64) 2 1-1-(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+64) 2 1-1-(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 1)) = 500170752*R^2 + 889067520*R + 395085728 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤500170752*R^2 + 889067520*R + 395085728 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 2) = 2526806016*R^2 + 4492422144*R + 1996775424 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2526806016*R^2 + 4492422144*R + 1996775424 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+64) 2 2-1-(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+64) 2 2-1-(oldEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) 2)) = 97844723712*R^3 + 258434924544*R^2 + 227511383040*R + 66756321280 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 258434924544*R^2 + 227511383040*R + 66756321280 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 2) = 5053612032*R^2 + 8984853504*R + 3993559040 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 8984853504*R + 3993559040 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+64) 2 2-1-(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+64) 2 2-1-(newEnds 8 4 (72*R+64) 2 (4*(72*R+64)-2) 6 (1024*R+902) true 2)) = 195689447424*R^3 + 516827381760*R^2 + 454947185664*R + 133479014400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 516827381760*R^2 + 454947185664*R + 133479014400 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+64)-2-1 := by
    have expansion : 8*(4*(72*R+64)-2-1) = 2304*R + 2024 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 2024 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+64)-2*(4*(72*R+64)-2) := by
    have expansion : 4*(T 8 4 (72*R+64)-2*(4*(72*R+64)-2)) = 6912*R + 6160 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 6160 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+902 := by
    have expansion : 8*(1024*R+902) = 8192*R + 7216 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 7216 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+64) 2-2-2*(1024*R+902) := by
    have expansion : 4*(Y 8 4 (72*R+64) 2-2-2*(1024*R+902)) = 28672*R + 25544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 25544 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_9 (R : ℕ) : Submask 6 (1024*R+902) := by
  exact submask_high_block 10 R 902 6 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_10 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 0) = 42467328*R^2 + 63650304*R + 23815472 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 63650304*R + 23815472 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+56) 2 0-1-(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+56) 2 0-1-(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 0)) = 297271296*R^2 + 465421824*R + 182164240 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤297271296*R^2 + 465421824*R + 182164240 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 0) = 169869312*R^2 + 259513344*R + 99082768 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 259513344*R + 99082768 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+56) 2 0-1-(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+56) 2 0-1-(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 0)) = 169869312*R^2 + 269558784*R + 106896944 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 269558784*R + 106896944 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 1) = 73138176*R^2 + 113847296*R + 44303600 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤73138176*R^2 + 113847296*R + 44303600 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+56) 2 1-1-(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+56) 2 1-1-(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 1)) = 1285816320*R^2 + 2000247808*R + 777909008 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1285816320*R^2 + 2000247808*R + 777909008 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 1) = 221773824*R^2 + 345390080*R + 134477040 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤221773824*R^2 + 345390080*R + 134477040 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+56) 2 1-1-(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+56) 2 1-1-(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 1)) = 2496135168*R^2 + 3882800128*R + 1509948176 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2496135168*R^2 + 3882800128*R + 1509948176 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 2) = 2526806016*R^2 + 3930909696*R + 1528812544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2526806016*R^2 + 3930909696*R + 1528812544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+56) 2 2-1-(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+56) 2 2-1-(oldEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) 2)) = 97844723712*R^3 + 225820016640*R^2 + 173705278464*R + 44533615616 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 225820016640*R^2 + 173705278464*R + 44533615616 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 2) = 5053612032*R^2 + 7861828608*R + 3057632256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 7861828608*R + 3057632256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+56) 2 2-1-(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+56) 2 2-1-(newEnds 8 4 (72*R+56) 2 (4*(72*R+56)-2) 6 (1024*R+783) true 2)) = 195689447424*R^3 + 451597565952*R^2 + 347344413696*R + 89041476608 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 451597565952*R^2 + 347344413696*R + 89041476608 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+56)-2-1 := by
    have expansion : 8*(4*(72*R+56)-2-1) = 2304*R + 1768 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 1768 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+56)-2*(4*(72*R+56)-2) := by
    have expansion : 4*(T 8 4 (72*R+56)-2*(4*(72*R+56)-2)) = 6912*R + 5392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 5392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+783 := by
    have expansion : 8*(1024*R+783) = 8192*R + 6264 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 6264 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+56) 2-2-2*(1024*R+783) := by
    have expansion : 4*(Y 8 4 (72*R+56) 2-2-2*(1024*R+783)) = 28672*R + 22400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 22400 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_10 (R : ℕ) : Submask 6 (1024*R+783) := by
  exact submask_high_block 10 R 783 6 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_11 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 0) = 42467328*R^2 + 44775936*R + 11768112 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 44775936*R + 11768112 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+40) 2 0-1-(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+40) 2 0-1-(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 0)) = 297271296*R^2 + 333301248*R + 93417232 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤297271296*R^2 + 333301248*R + 93417232 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 0) = 169869312*R^2 + 184015872*R + 49801744 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 184015872*R + 49801744 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+40) 2 0-1-(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+40) 2 0-1-(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 0)) = 169869312*R^2 + 194061312*R + 55383600 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 194061312*R + 55383600 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 1) = 561512448*R^2 + 624003072*R + 173361888 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤561512448*R^2 + 624003072*R + 173361888 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+40) 2 1-1-(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+40) 2 1-1-(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 1)) = 797442048*R^2 + 886112256*R + 246160672 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤797442048*R^2 + 886112256*R + 246160672 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 1) = 1198522368*R^2 + 1332123648*R + 370154208 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1198522368*R^2 + 1332123648*R + 370154208 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+40) 2 1-1-(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+40) 2 1-1-(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 1)) = 1519386624*R^2 + 1688107008*R + 468890912 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1519386624*R^2 + 1688107008*R + 468890912 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 2) = 2526806016*R^2 + 2807884800*R + 780057600 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2526806016*R^2 + 2807884800*R + 780057600 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+40) 2 2-1-(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+40) 2 2-1-(oldEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) 2)) = 97844723712*R^3 + 160590200832*R^2 + 87836341248*R + 16010306560 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 160590200832*R^2 + 87836341248*R + 16010306560 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 2) = 5053612032*R^2 + 5615778816*R + 1560120320 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 5615778816*R + 1560120320 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+40) 2 2-1-(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+40) 2 2-1-(newEnds 8 4 (72*R+40) 2 (4*(72*R+40)-2) 6 (1024*R+558) true 2)) = 195689447424*R^3 + 321137934336*R^2 + 175625413632*R + 32007459840 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 321137934336*R^2 + 175625413632*R + 32007459840 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+40)-2-1 := by
    have expansion : 8*(4*(72*R+40)-2-1) = 2304*R + 1256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 1256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+40)-2*(4*(72*R+40)-2) := by
    have expansion : 4*(T 8 4 (72*R+40)-2*(4*(72*R+40)-2)) = 6912*R + 3856 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 3856 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+558 := by
    have expansion : 8*(1024*R+558) = 8192*R + 4464 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 4464 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+40) 2-2-2*(1024*R+558) := by
    have expansion : 4*(Y 8 4 (72*R+40) 2-2-2*(1024*R+558)) = 28672*R + 16008 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 16008 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_11 (R : ℕ) : Submask 6 (1024*R+558) := by
  exact submask_high_block 10 R 558 6 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_12 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 0) = 84934656*R^2 + 15307776*R + 651904 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 15307776*R + 651904 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+8) 1 0-1-(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+8) 1 0-1-(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 0)) = 254803968*R^2 + 60779520*R + 3608000 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 60779520*R + 3608000 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 0) = 254803968*R^2 + 49600512*R + 2364624 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 49600512*R + 2364624 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+8) 1 0-1-(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+8) 1 0-1-(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 0)) = 84934656*R^2 + 26486784*R + 1895280 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 26486784*R + 1895280 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 1) = 94371840*R^2 + 21377024*R + 1209920 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤94371840*R^2 + 21377024*R + 1209920 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+8) 1 1-1-(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+8) 1 1-1-(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 1)) = 2623537152*R^2 + 582934528*R + 32381376 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2623537152*R^2 + 582934528*R + 32381376 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 1) = 264241152*R^2 + 59789312*R + 3380800 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤264241152*R^2 + 59789312*R + 3380800 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+8) 1 1-1-(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+8) 1 1-1-(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 1)) = 5171576832*R^2 + 1148833792*R + 63801792 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5171576832*R^2 + 1148833792*R + 63801792 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 2) = 5053612032*R^2 + 1123679232*R + 62462976 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 1123679232*R + 62462976 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+8) 1 2-1-(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+8) 1 2-1-(oldEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) 2)) = 195689447424*R^3 + 60218671104*R^2 + 6133588992*R + 206504960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 60218671104*R^2 + 6133588992*R + 206504960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 2) = 10107224064*R^2 + 2247367680*R + 124926976 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10107224064*R^2 + 2247367680*R + 124926976 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+8) 1 2-1-(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+8) 1 2-1-(newEnds 8 8 (72*R+8) 1 (8*(72*R+8)-3) 4 (1024*R+100) true 2)) = 391378894848*R^3 + 120394874880*R^2 + 12257657856*R + 412476416 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 120394874880*R^2 + 12257657856*R + 412476416 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+8)-3-1 := by
    have expansion : 8*(8*(72*R+8)-3-1) = 4608*R + 480 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 480 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+8)-2*(8*(72*R+8)-3) := by
    have expansion : 4*(T 8 8 (72*R+8)-2*(8*(72*R+8)-3)) = 13824*R + 1560 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 1560 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+100 := by
    have expansion : 8*(1024*R+100) = 8192*R + 800 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 800 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+8) 1-2-2*(1024*R+100) := by
    have expansion : 4*(Y 8 8 (72*R+8) 1-2-2*(1024*R+100)) = 28672*R + 3288 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 3288 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_12 (R : ℕ) : Submask 4 (1024*R+100) := by
  exact submask_high_block 10 R 100 4 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_13 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 0) = 84934656*R^2 + 34182144*R + 3401344 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 34182144*R + 3401344 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+16) 1 0-1-(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+16) 1 0-1-(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 0)) = 254803968*R^2 + 117402624*R + 13507008 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 117402624*R + 13507008 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 0) = 254803968*R^2 + 106223616*R + 11021520 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 106223616*R + 11021520 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+16) 1 0-1-(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+16) 1 0-1-(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 0)) = 84934656*R^2 + 45361152*R + 5886832 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 45361152*R + 5886832 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 1) = 179306496*R^2 + 80099328*R + 8944992 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤179306496*R^2 + 80099328*R + 8944992 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+16) 1 1-1-(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+16) 1 1-1-(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 1)) = 2538602496*R^2 + 1128192000*R + 125346464 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2538602496*R^2 + 1128192000*R + 125346464 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 1) = 434110464*R^2 + 194009088*R + 21675360 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤434110464*R^2 + 194009088*R + 21675360 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+16) 1 1-1-(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+16) 1 1-1-(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 1)) = 5001707520*R^2 + 2222573568*R + 246907552 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5001707520*R^2 + 2222573568*R + 246907552 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 2) = 5053612032*R^2 + 2246704128*R + 249706496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 2246704128*R + 249706496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+16) 1 2-1-(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+16) 1 2-1-(oldEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) 2)) = 195689447424*R^3 + 125448486912*R^2 + 26763273216*R + 1899890688 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 125448486912*R^2 + 26763273216*R + 1899890688 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 2) = 10107224064*R^2 + 4493417472*R + 499415040 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10107224064*R^2 + 4493417472*R + 499415040 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+16) 1 2-1-(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+16) 1 2-1-(newEnds 8 8 (72*R+16) 1 (8*(72*R+16)-3) 4 (1024*R+214) true 2)) = 391378894848*R^3 + 250854506496*R^2 + 53507589120*R + 3797665792 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 250854506496*R^2 + 53507589120*R + 3797665792 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+16)-3-1 := by
    have expansion : 8*(8*(72*R+16)-3-1) = 4608*R + 992 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 992 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+16)-2*(8*(72*R+16)-3) := by
    have expansion : 4*(T 8 8 (72*R+16)-2*(8*(72*R+16)-3)) = 13824*R + 3096 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 3096 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+214 := by
    have expansion : 8*(1024*R+214) = 8192*R + 1712 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 1712 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+16) 1-2-2*(1024*R+214) := by
    have expansion : 4*(Y 8 8 (72*R+16) 1-2-2*(1024*R+214)) = 28672*R + 6472 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 6472 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_13 (R : ℕ) : Submask 4 (1024*R+214) := by
  exact submask_high_block 10 R 214 4 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_14 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 0) = 84934656*R^2 + 71930880*R + 15191680 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 71930880*R + 15191680 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+32) 1 0-1-(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+32) 1 0-1-(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 0)) = 254803968*R^2 + 230648832*R + 52179392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 230648832*R + 52179392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 0) = 254803968*R^2 + 219469824*R + 47209680 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 219469824*R + 47209680 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+32) 1 0-1-(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+32) 1 0-1-(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 0)) = 84934656*R^2 + 83109888*R + 20161392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 83109888*R + 20161392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 1) = 1113587712*R^2 + 990285824*R + 220158912 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1113587712*R^2 + 990285824*R + 220158912 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+32) 1 1-1-(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+32) 1 1-1-(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 1)) = 1604321280*R^2 + 1425965056*R + 316859456 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1604321280*R^2 + 1425965056*R + 316859456 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 1) = 2302672896*R^2 + 2047913984*R + 455334848 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2302672896*R^2 + 2047913984*R + 455334848 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+32) 1 1-1-(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+32) 1 1-1-(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 1)) = 3133145088*R^2 + 2784587776*R + 618701888 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤3133145088*R^2 + 2784587776*R + 618701888 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 2) = 5053612032*R^2 + 4492753920*R + 998535168 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 4492753920*R + 998535168 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+32) 1 2-1-(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+32) 1 2-1-(oldEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) 2)) = 195689447424*R^3 + 255908118528*R^2 + 111509185536*R + 16189755392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 255908118528*R^2 + 111509185536*R + 16189755392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 2) = 10107224064*R^2 + 8985517056*R + 1997074432 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10107224064*R^2 + 8985517056*R + 1997074432 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+32) 1 2-1-(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+32) 1 2-1-(newEnds 8 8 (72*R+32) 1 (8*(72*R+32)-3) 4 (1024*R+444) true 2)) = 391378894848*R^3 + 511773769728*R^2 + 222980539392*R + 32371085312 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 511773769728*R^2 + 222980539392*R + 32371085312 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+32)-3-1 := by
    have expansion : 8*(8*(72*R+32)-3-1) = 4608*R + 2016 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 2016 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+32)-2*(8*(72*R+32)-3) := by
    have expansion : 4*(T 8 8 (72*R+32)-2*(8*(72*R+32)-3)) = 13824*R + 6168 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 6168 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+444 := by
    have expansion : 8*(1024*R+444) = 8192*R + 3552 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 3552 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+32) 1-2-2*(1024*R+444) := by
    have expansion : 4*(Y 8 8 (72*R+32) 1-2-2*(1024*R+444)) = 28672*R + 12824 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 12824 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_14 (R : ℕ) : Submask 4 (1024*R+444) := by
  exact submask_high_block 10 R 444 4 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_15 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 0) = 84934656*R^2 + 147428352*R + 63938176 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 147428352*R + 63938176 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+64) 1 0-1-(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+64) 1 0-1-(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 0)) = 254803968*R^2 + 457141248*R + 205021632 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 457141248*R + 205021632 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 0) = 254803968*R^2 + 445962240*R + 195083472 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 445962240*R + 195083472 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+64) 1 0-1-(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+64) 1 0-1-(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 0)) = 84934656*R^2 + 158607360*R + 73876336 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 158607360*R + 73876336 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 1) = 1453326336*R^2 + 2584129536*R + 1148696640 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1453326336*R^2 + 2584129536*R + 1148696640 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+64) 1 1-1-(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+64) 1 1-1-(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 1)) = 1264582656*R^2 + 2248040448*R + 999081920 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1264582656*R^2 + 2248040448*R + 999081920 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 1) = 2982150144*R^2 + 5302702080*R + 2357246016 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2982150144*R^2 + 5302702080*R + 2357246016 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+64) 1 1-1-(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+64) 1 1-1-(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 1)) = 2453667840*R^2 + 4361637888*R + 1938311104 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2453667840*R^2 + 4361637888*R + 1938311104 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 2) = 5053612032*R^2 + 8984853504*R + 3993559040 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 8984853504*R + 3993559040 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+64) 1 2-1-(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+64) 1 2-1-(oldEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) 2)) = 195689447424*R^3 + 516827381760*R^2 + 454947185664*R + 133479014400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 516827381760*R^2 + 454947185664*R + 133479014400 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 2) = 10107224064*R^2 + 17969716224*R + 7987126272 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10107224064*R^2 + 17969716224*R + 7987126272 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+64) 1 2-1-(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+64) 1 2-1-(newEnds 8 8 (72*R+64) 1 (8*(72*R+64)-3) 4 (1024*R+900) true 2)) = 391378894848*R^3 + 1033612296192*R^2 + 909818790912*R + 266924400640 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 1033612296192*R^2 + 909818790912*R + 266924400640 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+64)-3-1 := by
    have expansion : 8*(8*(72*R+64)-3-1) = 4608*R + 4064 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 4064 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+64)-2*(8*(72*R+64)-3) := by
    have expansion : 4*(T 8 8 (72*R+64)-2*(8*(72*R+64)-3)) = 13824*R + 12312 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 12312 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+900 := by
    have expansion : 8*(1024*R+900) = 8192*R + 7200 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 7200 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+64) 1-2-2*(1024*R+900) := by
    have expansion : 4*(Y 8 8 (72*R+64) 1-2-2*(1024*R+900)) = 28672*R + 25560 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 25560 := by positivity
    nlinarith only [expansion,nonnegative]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    fin_cases r
    · exact ⟨hS1_lower,sub_nonneg.mp hS1_upper,hT1_lower,sub_nonneg.mp hT1_upper⟩
    · exact ⟨hS2_lower,sub_nonneg.mp hS2_upper,hT2_lower,sub_nonneg.mp hT2_upper⟩
    · exact ⟨hS3_lower,sub_nonneg.mp hS3_upper,hT3_lower,sub_nonneg.mp hT3_upper⟩
  · linarith only [hv_lower]
  · linarith only [hv_upper]
  · exact hM_lower
  · linarith only [hM_upper]

theorem residue_submask_15 (R : ℕ) : Submask 4 (1024*R+900) := by
  exact submask_high_block 10 R 900 4 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
