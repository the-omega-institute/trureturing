/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/ResidueCertificates1
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

theorem residue_bounds_0 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 0) = 21233664*R^2 + 3534336*R + 130304 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤21233664*R^2 + 3534336*R + 130304 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+8) 1 0-1-(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+8) 1 0-1-(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 0)) = 148635648*R^2 + 34509312*R + 1999680 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤148635648*R^2 + 34509312*R + 1999680 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 0) = 84934656*R^2 + 16551936*R + 789984 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 16551936*R + 789984 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+8) 1 0-1-(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+8) 1 0-1-(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 0)) = 84934656*R^2 + 21491712*R + 1340000 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 21491712*R + 1340000 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 1) = 195821568*R^2 + 43727872*R + 2441008 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195821568*R^2 + 43727872*R + 2441008 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+8) 1 1-1-(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+8) 1 1-1-(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 1)) = 483655680*R^2 + 107432960*R + 5966032 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤483655680*R^2 + 107432960*R + 5966032 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 1) = 429391872*R^2 + 95964160*R + 5361456 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤429391872*R^2 + 95964160*R + 5361456 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+8) 1 1-1-(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+8) 1 1-1-(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 1)) = 929562624*R^2 + 206357504*R + 11452624 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤929562624*R^2 + 206357504*R + 11452624 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 2) = 1167851520*R^2 + 259845120*R + 14453760 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1167851520*R^2 + 259845120*R + 14453760 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+8) 1 2-1-(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+8) 1 2-1-(oldEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) 2)) = 48922361856*R^3 + 15160836096*R^2 + 1556849664*R + 52921344 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤48922361856*R^3 + 15160836096*R^2 + 1556849664*R + 52921344 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 2) = 2335703040*R^2 + 519699456*R + 28908544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2335703040*R^2 + 519699456*R + 28908544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+8) 1 2-1-(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+8) 1 2-1-(newEnds 8 4 (72*R+8) 1 (4*(72*R+8)-2) 3 (512*R+51) true 2)) = 97844723712*R^3 + 30300438528*R^2 + 3108934656*R + 105575424 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 30300438528*R^2 + 3108934656*R + 105575424 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+8)-2-1 := by
    have expansion : 8*(4*(72*R+8)-2-1) = 2304*R + 232 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 232 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+8)-2*(4*(72*R+8)-2) := by
    have expansion : 4*(T 8 4 (72*R+8)-2*(4*(72*R+8)-2)) = 6912*R + 784 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 784 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤512*R+51 := by
    have expansion : 8*(512*R+51) = 4096*R + 408 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4096*R + 408 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+8) 1-2-2*(512*R+51) := by
    have expansion : 4*(Y 8 4 (72*R+8) 1-2-2*(512*R+51)) = 14336*R + 1632 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤14336*R + 1632 := by positivity
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

theorem residue_submask_0 (R : ℕ) : Submask 3 (512*R+51) := by
  exact submask_high_block 9 R 51 3 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_1 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 0) = 21233664*R^2 + 8252928*R + 785152 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤21233664*R^2 + 8252928*R + 785152 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+16) 1 0-1-(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+16) 1 0-1-(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 0)) = 148635648*R^2 + 67539456*R + 7669056 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤148635648*R^2 + 67539456*R + 7669056 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 0) = 84934656*R^2 + 35426304*R + 3677664 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 35426304*R + 3677664 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+16) 1 0-1-(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+16) 1 0-1-(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 0)) = 84934656*R^2 + 40366080*R + 4776544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 40366080*R + 4776544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 1) = 25952256*R^2 + 11738112*R + 1326768 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤25952256*R^2 + 11738112*R + 1326768 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+16) 1 1-1-(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+16) 1 1-1-(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 1)) = 653524992*R^2 + 290417664*R + 32264528 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤653524992*R^2 + 290417664*R + 32264528 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 1) = 89653248*R^2 + 40381440*R + 4546224 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤89653248*R^2 + 40381440*R + 4546224 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+16) 1 1-1-(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+16) 1 1-1-(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 1)) = 1269301248*R^2 + 563930112*R + 62636368 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1269301248*R^2 + 563930112*R + 62636368 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 2) = 1167851520*R^2 + 519367680*R + 57743360 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1167851520*R^2 + 519367680*R + 57743360 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+16) 1 2-1-(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+16) 1 2-1-(oldEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) 2)) = 48922361856*R^3 + 31468290048*R^2 + 6737863680*R + 480184320 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤48922361856*R^3 + 31468290048*R^2 + 6737863680*R + 480184320 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 2) = 2335703040*R^2 + 1038744576*R + 115488768 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2335703040*R^2 + 1038744576*R + 115488768 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+16) 1 2-1-(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+16) 1 2-1-(newEnds 8 4 (72*R+16) 1 (4*(72*R+16)-2) 3 (512*R+107) true 2)) = 97844723712*R^3 + 62915346432*R^2 + 13466244096*R + 959309824 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 62915346432*R^2 + 13466244096*R + 959309824 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+16)-2-1 := by
    have expansion : 8*(4*(72*R+16)-2-1) = 2304*R + 488 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 488 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+16)-2*(4*(72*R+16)-2) := by
    have expansion : 4*(T 8 4 (72*R+16)-2*(4*(72*R+16)-2)) = 6912*R + 1552 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 1552 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤512*R+107 := by
    have expansion : 8*(512*R+107) = 4096*R + 856 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4096*R + 856 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+16) 1-2-2*(512*R+107) := by
    have expansion : 4*(Y 8 4 (72*R+16) 1-2-2*(512*R+107)) = 14336*R + 3232 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤14336*R + 3232 := by positivity
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

theorem residue_submask_1 (R : ℕ) : Submask 3 (512*R+107) := by
  exact submask_high_block 9 R 107 3 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_2 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 0) = 21233664*R^2 + 17690112*R + 3667712 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤21233664*R^2 + 17690112*R + 3667712 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+32) 1 0-1-(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+32) 1 0-1-(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 0)) = 148635648*R^2 + 133599744*R + 30017856 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤148635648*R^2 + 133599744*R + 30017856 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 0) = 84934656*R^2 + 73175040*R + 15744480 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 73175040*R + 15744480 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+32) 1 0-1-(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+32) 1 0-1-(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 0)) = 84934656*R^2 + 78114816*R + 17941088 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 78114816*R + 17941088 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 1) = 450625536*R^2 + 400780288*R + 89112048 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤450625536*R^2 + 400780288*R + 89112048 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+32) 1 1-1-(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+32) 1 1-1-(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 1)) = 228851712*R^2 + 203365376*R + 45179408 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤228851712*R^2 + 203365376*R + 45179408 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 1) = 938999808*R^2 + 835222528*R + 185728496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤938999808*R^2 + 835222528*R + 185728496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+32) 1 1-1-(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+32) 1 1-1-(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 1)) = 419954688*R^2 + 373068800*R + 82854416 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤419954688*R^2 + 373068800*R + 82854416 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 2) = 1167851520*R^2 + 1038412800*R + 230830080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1167851520*R^2 + 1038412800*R + 230830080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+32) 1 2-1-(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+32) 1 2-1-(oldEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) 2)) = 48922361856*R^3 + 64083197952*R^2 + 27971527680*R + 4068347904 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤48922361856*R^3 + 64083197952*R^2 + 27971527680*R + 4068347904 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 2) = 2335703040*R^2 + 2076834816*R + 461664256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2335703040*R^2 + 2076834816*R + 461664256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+32) 1 2-1-(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+32) 1 2-1-(newEnds 8 4 (72*R+32) 1 (4*(72*R+32)-2) 3 (512*R+223) true 2)) = 97844723712*R^3 + 128145162240*R^2 + 55924134912*R + 8132481024 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 128145162240*R^2 + 55924134912*R + 8132481024 := by positivity
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
  have hM_lower : 0≤512*R+223 := by
    have expansion : 8*(512*R+223) = 4096*R + 1784 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4096*R + 1784 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+32) 1-2-2*(512*R+223) := by
    have expansion : 4*(Y 8 4 (72*R+32) 1-2-2*(512*R+223)) = 14336*R + 6400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤14336*R + 6400 := by positivity
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

theorem residue_submask_2 (R : ℕ) : Submask 3 (512*R+223) := by
  exact submask_high_block 9 R 223 3 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_3 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 0) = 21233664*R^2 + 36564480*R + 15724288 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤21233664*R^2 + 36564480*R + 15724288 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+64) 1 0-1-(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+64) 1 0-1-(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 0)) = 148635648*R^2 + 265720320*R + 118755648 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤148635648*R^2 + 265720320*R + 118755648 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 0) = 84934656*R^2 + 148672512*R + 65043936 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 148672512*R + 65043936 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+64) 1 0-1-(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+64) 1 0-1-(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 0)) = 84934656*R^2 + 153612288*R + 69436000 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 153612288*R + 69436000 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 1) = 535560192*R^2 + 952335360*R + 423361584 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤535560192*R^2 + 952335360*R + 423361584 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+64) 1 1-1-(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+64) 1 1-1-(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 1)) = 143917056*R^2 + 255790080*R + 113656784 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤143917056*R^2 + 255790080*R + 113656784 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 1) = 1108869120*R^2 + 1971883008*R + 876641328 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1108869120*R^2 + 1971883008*R + 876641328 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+64) 1 1-1-(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+64) 1 1-1-(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 1)) = 250085376*R^2 + 444367872*R + 197395408 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤250085376*R^2 + 444367872*R + 197395408 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 2) = 1167851520*R^2 + 2076503040*R + 923033600 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1167851520*R^2 + 2076503040*R + 923033600 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+64) 1 2-1-(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+64) 1 2-1-(oldEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) 2)) = 48922361856*R^3 + 129313013760*R^2 + 113925399552*R + 33453514752 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤48922361856*R^3 + 129313013760*R^2 + 113925399552*R + 33453514752 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 2) = 2335703040*R^2 + 4153015296*R + 1846075392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2335703040*R^2 + 4153015296*R + 1846075392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+64) 1 2-1-(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+64) 1 2-1-(newEnds 8 4 (72*R+64) 1 (4*(72*R+64)-2) 3 (512*R+451) true 2)) = 97844723712*R^3 + 258604793856*R^2 + 227813004288*R + 66890211328 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 258604793856*R^2 + 227813004288*R + 66890211328 := by positivity
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
  have hM_lower : 0≤512*R+451 := by
    have expansion : 8*(512*R+451) = 4096*R + 3608 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4096*R + 3608 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+64) 1-2-2*(512*R+451) := by
    have expansion : 4*(Y 8 4 (72*R+64) 1-2-2*(512*R+451)) = 14336*R + 12768 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤14336*R + 12768 := by positivity
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

theorem residue_submask_3 (R : ℕ) : Submask 3 (512*R+451) := by
  exact submask_high_block 9 R 451 3 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_4 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 0) = 169869312*R^2 + 263637504*R + 102290816 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 263637504*R + 102290816 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+56) 1 0-1-(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+56) 1 0-1-(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 0)) = 898560*R + 699072 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤898560*R + 699072 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 0) = 42467328*R^2 + 64318464*R + 24334944 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 64318464*R + 24334944 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+56) 1 0-1-(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+56) 1 0-1-(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 0)) = 127401984*R^2 + 200217600*R + 78654944 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤127401984*R^2 + 200217600*R + 78654944 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 1) = 514326528*R^2 + 800290816*R + 311312544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤514326528*R^2 + 800290816*R + 311312544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+56) 1 1-1-(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+56) 1 1-1-(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 1)) = 165150720*R^2 + 256839680*R + 99858272 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤165150720*R^2 + 256839680*R + 99858272 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 1) = 1066401792*R^2 + 1659406336*R + 645542048 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1066401792*R^2 + 1659406336*R + 645542048 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+56) 1 1-1-(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+56) 1 1-1-(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 1)) = 292552704*R^2 + 454854656*R + 176799584 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤292552704*R^2 + 454854656*R + 176799584 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 2) = 1167851520*R^2 + 1816980480*R + 706728960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1167851520*R^2 + 1816980480*R + 706728960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+56) 1 2-1-(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+56) 1 2-1-(oldEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) 2)) = 48922361856*R^3 + 113005559808*R^2 + 87001113600*R + 22324485120 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤48922361856*R^3 + 113005559808*R^2 + 87001113600*R + 22324485120 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 2) = 2335703040*R^2 + 3633970176*R + 1413465088 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2335703040*R^2 + 3633970176*R + 1413465088 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+56) 1 2-1-(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+56) 1 2-1-(newEnds 8 4 (72*R+56) 1 (4*(72*R+56)-1) 2 (512*R+394) false 2)) = 97844723712*R^3 + 225989885952*R^2 + 173969150976*R + 44636089344 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 225989885952*R^2 + 173969150976*R + 44636089344 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+56)-1-1 := by
    have expansion : 8*(4*(72*R+56)-1-1) = 2304*R + 1776 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 1776 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+56)-2*(4*(72*R+56)-1) := by
    have expansion : 4*(T 8 4 (72*R+56)-2*(4*(72*R+56)-1)) = 6912*R + 5384 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 5384 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤512*R+394 := by
    have expansion : 8*(512*R+394) = 4096*R + 3152 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4096*R + 3152 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+56) 1-2-2*(512*R+394) := by
    have expansion : 4*(Y 8 4 (72*R+56) 1-2-2*(512*R+394)) = 14336*R + 11176 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤14336*R + 11176 := by positivity
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

theorem residue_submask_4 (R : ℕ) : Submask 2 (512*R+394) := by
  exact submask_high_block 9 R 394 2 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_5 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 0) = 21233664*R^2 + 22408704*R + 5895424 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤21233664*R^2 + 22408704*R + 5895424 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+40) 1 0-1-(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+40) 1 0-1-(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 0)) = 148635648*R^2 + 166629888*R + 46697280 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤148635648*R^2 + 166629888*R + 46697280 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 0) = 84934656*R^2 + 92049408*R + 24923616 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 92049408*R + 24923616 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+40) 1 0-1-(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+40) 1 0-1-(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 0)) = 84934656*R^2 + 96989184*R + 27669088 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 96989184*R + 27669088 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 1) = 280756224*R^2 + 312167424*R + 86773104 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤280756224*R^2 + 312167424*R + 86773104 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+40) 1 1-1-(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+40) 1 1-1-(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 1)) = 398721024*R^2 + 442973184*R + 123034256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤398721024*R^2 + 442973184*R + 123034256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 1) = 599261184*R^2 + 666393600*R + 185261424 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤599261184*R^2 + 666393600*R + 185261424 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+40) 1 1-1-(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+40) 1 1-1-(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 1)) = 759693312*R^2 + 843887616*R + 234353296 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤759693312*R^2 + 843887616*R + 234353296 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 2) = 1167851520*R^2 + 1297935360*R + 360627200 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1167851520*R^2 + 1297935360*R + 360627200 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+40) 1 2-1-(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+40) 1 2-1-(oldEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) 2)) = 48922361856*R^3 + 80390651904*R^2 + 44024177664*R + 8034554880 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤48922361856*R^3 + 80390651904*R^2 + 44024177664*R + 8034554880 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 2) = 2335703040*R^2 + 2595879936*R + 721259520 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2335703040*R^2 + 2595879936*R + 721259520 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+40) 1 2-1-(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+40) 1 2-1-(newEnds 8 4 (72*R+40) 1 (4*(72*R+40)-2) 3 (512*R+279) true 2)) = 97844723712*R^3 + 160760070144*R^2 + 88024716288*R + 16062530560 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 160760070144*R^2 + 88024716288*R + 16062530560 := by positivity
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
  have hM_lower : 0≤512*R+279 := by
    have expansion : 8*(512*R+279) = 4096*R + 2232 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4096*R + 2232 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+40) 1-2-2*(512*R+279) := by
    have expansion : 4*(Y 8 4 (72*R+40) 1-2-2*(512*R+279)) = 14336*R + 8000 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤14336*R + 8000 := by positivity
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

theorem residue_submask_5 (R : ℕ) : Submask 3 (512*R+279) := by
  exact submask_high_block 9 R 279 3 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_6 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 0) = 42467328*R^2 + 7027200*R + 256304 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 7027200*R + 256304 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+8) 2 0-1-(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+8) 2 0-1-(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 0)) = 297271296*R^2 + 69060096*R + 4003600 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤297271296*R^2 + 69060096*R + 4003600 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 0) = 169869312*R^2 + 33020928*R + 1571344 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 33020928*R + 1571344 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+8) 2 0-1-(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+8) 2 0-1-(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 0)) = 169869312*R^2 + 43066368*R + 2688560 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 43066368*R + 2688560 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 1) = 391643136*R^2 + 87123968*R + 4845152 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391643136*R^2 + 87123968*R + 4845152 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+8) 2 1-1-(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+8) 2 1-1-(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 1)) = 967311360*R^2 + 215031808*R + 11950496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤967311360*R^2 + 215031808*R + 11950496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 1) = 858783744*R^2 + 191264768*R + 10649184 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤858783744*R^2 + 191264768*R + 10649184 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+8) 2 1-1-(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+8) 2 1-1-(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 1)) = 1859125248*R^2 + 413046784*R + 22942112 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1859125248*R^2 + 413046784*R + 22942112 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 2) = 2526806016*R^2 + 561835008*R + 31230976 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2526806016*R^2 + 561835008*R + 31230976 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+8) 2 2-1-(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+8) 2 2-1-(oldEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) 2)) = 97844723712*R^3 + 30130569216*R^2 + 3071554560*R + 103519232 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 30130569216*R^2 + 3071554560*R + 103519232 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 2) = 5053612032*R^2 + 1123679232*R + 62462976 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 1123679232*R + 62462976 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+8) 2 2-1-(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+8) 2 2-1-(newEnds 8 4 (72*R+8) 2 (4*(72*R+8)-2) 6 (1024*R+102) true 2)) = 195689447424*R^3 + 60218671104*R^2 + 6133588992*R + 206504960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 60218671104*R^2 + 6133588992*R + 206504960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+8)-2-1 := by
    have expansion : 8*(4*(72*R+8)-2-1) = 2304*R + 232 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 232 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+8)-2*(4*(72*R+8)-2) := by
    have expansion : 4*(T 8 4 (72*R+8)-2*(4*(72*R+8)-2)) = 6912*R + 784 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 784 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+102 := by
    have expansion : 8*(1024*R+102) = 8192*R + 816 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 816 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+8) 2-2-2*(1024*R+102) := by
    have expansion : 4*(Y 8 4 (72*R+8) 2-2-2*(1024*R+102)) = 28672*R + 3272 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 3272 := by positivity
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

theorem residue_submask_6 (R : ℕ) : Submask 6 (1024*R+102) := by
  exact submask_high_block 10 R 102 6 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_7 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true := by
  have hS1_lower : 0≤oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 0 := by
    have expansion : 8*(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 0) = 42467328*R^2 + 16464384*R + 1561392 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤42467328*R^2 + 16464384*R + 1561392 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 4 (72*R+16) 2 0-1-(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 0) := by
    have expansion : 8*(oldHeads 8 4 (72*R+16) 2 0-1-(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 0)) = 297271296*R^2 + 135120384*R + 15346960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤297271296*R^2 + 135120384*R + 15346960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 0 := by
    have expansion : 8*(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 0) = 169869312*R^2 + 70769664*R + 7337488 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 70769664*R + 7337488 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 4 (72*R+16) 2 0-1-(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 0) := by
    have expansion : 8*(newHeads 8 4 (72*R+16) 2 0-1-(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 0)) = 169869312*R^2 + 80815104*R + 9570864 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤169869312*R^2 + 80815104*R + 9570864 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 1 := by
    have expansion : 8*(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 1) = 51904512*R^2 + 23144448*R + 2579808 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤51904512*R^2 + 23144448*R + 2579808 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 4 (72*R+16) 2 1-1-(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 1) := by
    have expansion : 8*(oldHeads 8 4 (72*R+16) 2 1-1-(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 1)) = 1307049984*R^2 + 581001216*R + 64565920 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1307049984*R^2 + 581001216*R + 64565920 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 1 := by
    have expansion : 8*(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 1) = 179306496*R^2 + 80099328*R + 8944992 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤179306496*R^2 + 80099328*R + 8944992 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 4 (72*R+16) 2 1-1-(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 1) := by
    have expansion : 8*(newHeads 8 4 (72*R+16) 2 1-1-(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 1)) = 2538602496*R^2 + 1128192000*R + 125346464 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2538602496*R^2 + 1128192000*R + 125346464 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 2 := by
    have expansion : 8*(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 2) = 2526806016*R^2 + 1123347456*R + 124852224 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2526806016*R^2 + 1123347456*R + 124852224 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 4 (72*R+16) 2 2-1-(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 2) := by
    have expansion : 8*(oldHeads 8 4 (72*R+16) 2 2-1-(oldEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) 2)) = 97844723712*R^3 + 62745477120*R^2 + 13391115264*R + 951003136 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤97844723712*R^3 + 62745477120*R^2 + 13391115264*R + 951003136 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 2 := by
    have expansion : 8*(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 2) = 5053612032*R^2 + 2246704128*R + 249706496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 2246704128*R + 249706496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 4 (72*R+16) 2 2-1-(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 2) := by
    have expansion : 8*(newHeads 8 4 (72*R+16) 2 2-1-(newEnds 8 4 (72*R+16) 2 (4*(72*R+16)-2) 6 (1024*R+214) true 2)) = 195689447424*R^3 + 125448486912*R^2 + 26763273216*R + 1899890688 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 125448486912*R^2 + 26763273216*R + 1899890688 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤4*(72*R+16)-2-1 := by
    have expansion : 8*(4*(72*R+16)-2-1) = 2304*R + 488 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2304*R + 488 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 4 (72*R+16)-2*(4*(72*R+16)-2) := by
    have expansion : 4*(T 8 4 (72*R+16)-2*(4*(72*R+16)-2)) = 6912*R + 1552 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤6912*R + 1552 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+214 := by
    have expansion : 8*(1024*R+214) = 8192*R + 1712 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 1712 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 4 (72*R+16) 2-2-2*(1024*R+214) := by
    have expansion : 4*(Y 8 4 (72*R+16) 2-2-2*(1024*R+214)) = 28672*R + 6472 := by
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

theorem residue_submask_7 (R : ℕ) : Submask 6 (1024*R+214) := by
  exact submask_high_block 10 R 214 6 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
