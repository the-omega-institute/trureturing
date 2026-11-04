/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/ResidueCertificates3
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

theorem residue_bounds_16 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 0) = 84934656*R^2 + 128553984*R + 48605824 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 128553984*R + 48605824 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+56) 1 0-1-(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+56) 1 0-1-(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 0)) = 254803968*R^2 + 400518144*R + 157373888 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 400518144*R + 157373888 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 0) = 254803968*R^2 + 389339136*R + 148677840 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 389339136*R + 148677840 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+56) 1 0-1-(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+56) 1 0-1-(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 0)) = 84934656*R^2 + 139732992*R + 57301872 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 139732992*R + 57301872 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 1) = 221773824*R^2 + 345390080*R + 134477040 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤221773824*R^2 + 345390080*R + 134477040 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+56) 1 1-1-(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+56) 1 1-1-(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 1)) = 2496135168*R^2 + 3882800128*R + 1509948176 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2496135168*R^2 + 3882800128*R + 1509948176 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 1) = 519045120*R^2 + 808475648*R + 314823920 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤519045120*R^2 + 808475648*R + 314823920 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+56) 1 1-1-(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+56) 1 1-1-(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 1)) = 4916772864*R^2 + 7647904768*R + 2974026512 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4916772864*R^2 + 7647904768*R + 2974026512 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 2) = 5053612032*R^2 + 7861828608*R + 3057632256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 7861828608*R + 3057632256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+56) 1 2-1-(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+56) 1 2-1-(oldEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) 2)) = 195689447424*R^3 + 451597565952*R^2 + 347344413696*R + 89041476608 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 451597565952*R^2 + 347344413696*R + 89041476608 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 2) = 10107224064*R^2 + 15723666432*R + 6115271680 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10107224064*R^2 + 15723666432*R + 6115271680 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+56) 1 2-1-(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+56) 1 2-1-(newEnds 8 8 (72*R+56) 1 (8*(72*R+56)-3) 4 (1024*R+783) true 2)) = 391378894848*R^3 + 903152664576*R^2 + 694622684160*R + 178057198592 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 903152664576*R^2 + 694622684160*R + 178057198592 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+56)-3-1 := by
    have expansion : 8*(8*(72*R+56)-3-1) = 4608*R + 3552 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 3552 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+56)-2*(8*(72*R+56)-3) := by
    have expansion : 4*(T 8 8 (72*R+56)-2*(8*(72*R+56)-3)) = 13824*R + 10776 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 10776 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+783 := by
    have expansion : 8*(1024*R+783) = 8192*R + 6264 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 6264 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+56) 1-2-2*(1024*R+783) := by
    have expansion : 4*(Y 8 8 (72*R+56) 1-2-2*(1024*R+783)) = 28672*R + 22400 := by
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

theorem residue_submask_16 (R : ℕ) : Submask 4 (1024*R+783) := by
  exact submask_high_block 10 R 783 4 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_17 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 0) = 84934656*R^2 + 90805248*R + 24232576 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 90805248*R + 24232576 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+40) 1 0-1-(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+40) 1 0-1-(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 0)) = 254803968*R^2 + 287271936*R + 80952768 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 287271936*R + 80952768 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 0) = 254803968*R^2 + 276092928*R + 74740944 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤254803968*R^2 + 276092928*R + 74740944 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+40) 1 0-1-(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+40) 1 0-1-(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 0)) = 84934656*R^2 + 101984256*R + 30444400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 101984256*R + 30444400 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 1) = 434110464*R^2 + 482758656*R + 134214336 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤434110464*R^2 + 482758656*R + 134214336 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+40) 1 1-1-(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+40) 1 1-1-(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 1)) = 2283798528*R^2 + 2537472000*R + 704830784 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤2283798528*R^2 + 2537472000*R + 704830784 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 1) = 943718400*R^2 + 1049653248*R + 291869376 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤943718400*R^2 + 1049653248*R + 291869376 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+40) 1 1-1-(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+40) 1 1-1-(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 1)) = 4492099584*R^2 + 4990808064*R + 1386220864 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4492099584*R^2 + 4990808064*R + 1386220864 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 2) = 5053612032*R^2 + 5615778816*R + 1560120320 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5053612032*R^2 + 5615778816*R + 1560120320 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+40) 1 2-1-(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+40) 1 2-1-(oldEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) 2)) = 195689447424*R^3 + 321137934336*R^2 + 175625413632*R + 32007459840 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤195689447424*R^3 + 321137934336*R^2 + 175625413632*R + 32007459840 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 2) = 10107224064*R^2 + 11231566848*R + 3120245760 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10107224064*R^2 + 11231566848*R + 3120245760 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+40) 1 2-1-(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+40) 1 2-1-(newEnds 8 8 (72*R+40) 1 (8*(72*R+40)-3) 4 (1024*R+556) true 2)) = 391378894848*R^3 + 642233401344*R^2 + 351203558400*R + 64001766400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 642233401344*R^2 + 351203558400*R + 64001766400 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+40)-3-1 := by
    have expansion : 8*(8*(72*R+40)-3-1) = 4608*R + 2528 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 2528 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+40)-2*(8*(72*R+40)-3) := by
    have expansion : 4*(T 8 8 (72*R+40)-2*(8*(72*R+40)-3)) = 13824*R + 7704 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 7704 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤1024*R+556 := by
    have expansion : 8*(1024*R+556) = 8192*R + 4448 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤8192*R + 4448 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+40) 1-2-2*(1024*R+556) := by
    have expansion : 4*(Y 8 8 (72*R+40) 1-2-2*(1024*R+556)) = 28672*R + 16024 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤28672*R + 16024 := by positivity
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

theorem residue_submask_17 (R : ℕ) : Submask 4 (1024*R+556) := by
  exact submask_high_block 10 R 556 4 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_18 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 0) = 212336640*R^2 + 44623872*R + 2336624 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤212336640*R^2 + 44623872*R + 2336624 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+8) 2 0-1-(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+8) 2 0-1-(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 0)) = 467140608*R^2 + 107550720*R + 6183120 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤467140608*R^2 + 107550720*R + 6183120 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 0) = 594542592*R^2 + 127282176*R + 6802144 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤594542592*R^2 + 127282176*R + 6802144 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+8) 2 0-1-(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+8) 2 0-1-(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 0)) = 84934656*R^2 + 24892416*R + 1717600 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 24892416*R + 1717600 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 1) = 570949632*R^2 + 127034368*R + 7065744 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤570949632*R^2 + 127034368*R + 7065744 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+8) 2 1-1-(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+8) 2 1-1-(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 1)) = 4864868352*R^2 + 1081256960*R + 60079984 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4864868352*R^2 + 1081256960*R + 60079984 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 1) = 1292894208*R^2 + 288130048*R + 16052368 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1292894208*R^2 + 288130048*R + 16052368 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+8) 2 1-1-(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+8) 2 1-1-(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 1)) = 9578741760*R^2 + 2128452608*R + 118239088 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤9578741760*R^2 + 2128452608*R + 118239088 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 2) = 10489430016*R^2 + 2331638784*R + 129571840 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10489430016*R^2 + 2331638784*R + 129571840 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+8) 2 2-1-(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+8) 2 2-1-(oldEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) 2)) = 391378894848*R^3 + 120055136256*R^2 + 12182897664*R + 408364032 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 120055136256*R^2 + 12182897664*R + 408364032 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 2) = 20978860032*R^2 + 4663286784*R + 259144704 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤20978860032*R^2 + 4663286784*R + 259144704 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+8) 2 2-1-(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+8) 2 2-1-(newEnds 8 8 (72*R+8) 2 (8*(72*R+8)-1) 1 (2048*R+201) true 2)) = 782757789696*R^3 + 240025337856*R^2 + 24346764288*R + 815662080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤782757789696*R^3 + 240025337856*R^2 + 24346764288*R + 815662080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+8)-1-1 := by
    have expansion : 8*(8*(72*R+8)-1-1) = 4608*R + 496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+8)-2*(8*(72*R+8)-1) := by
    have expansion : 4*(T 8 8 (72*R+8)-2*(8*(72*R+8)-1)) = 13824*R + 1544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 1544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤2048*R+201 := by
    have expansion : 8*(2048*R+201) = 16384*R + 1608 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤16384*R + 1608 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+8) 2-2-2*(2048*R+201) := by
    have expansion : 4*(Y 8 8 (72*R+8) 2-2-2*(2048*R+201)) = 57344*R + 6576 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤57344*R + 6576 := by positivity
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

theorem residue_submask_18 (R : ℕ) : Submask 1 (2048*R+201) := by
  exact submask_high_block 11 R 201 1 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_19 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 0) = 212336640*R^2 + 91809792*R + 9916272 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤212336640*R^2 + 91809792*R + 9916272 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+16) 2 0-1-(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+16) 2 0-1-(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 0)) = 467140608*R^2 + 211359744*R + 23900368 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤467140608*R^2 + 211359744*R + 23900368 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 0) = 594542592*R^2 + 259402752*R + 28284640 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤594542592*R^2 + 259402752*R + 28284640 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+16) 2 0-1-(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+16) 2 0-1-(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 0)) = 84934656*R^2 + 43766784*R + 5532000 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 43766784*R + 5532000 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 1) = 740818944*R^2 + 329413632*R + 36618960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤740818944*R^2 + 329413632*R + 36618960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+16) 2 1-1-(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+16) 2 1-1-(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 1)) = 4694999040*R^2 + 2086837248*R + 231890224 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4694999040*R^2 + 2086837248*R + 231890224 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 1) = 1632632832*R^2 + 726438912*R + 80806608 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1632632832*R^2 + 726438912*R + 80806608 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+16) 2 1-1-(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+16) 2 1-1-(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 1)) = 9239003136*R^2 + 4106062848*R + 456211760 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤9239003136*R^2 + 4106062848*R + 456211760 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 2) = 10489430016*R^2 + 4662623232*R + 518141952 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10489430016*R^2 + 4662623232*R + 518141952 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+16) 2 2-1-(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+16) 2 2-1-(oldEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) 2)) = 391378894848*R^3 + 250514767872*R^2 + 53357331456*R + 3781052416 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 250514767872*R^2 + 53357331456*R + 3781052416 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 2) = 20978860032*R^2 + 9325255680*R + 1036285952 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤20978860032*R^2 + 9325255680*R + 1036285952 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+16) 2 2-1-(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+16) 2 2-1-(newEnds 8 8 (72*R+16) 2 (8*(72*R+16)-1) 1 (2048*R+429) true 2)) = 782757789696*R^3 + 500944601088*R^2 + 106676757504*R + 7557875712 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤782757789696*R^3 + 500944601088*R^2 + 106676757504*R + 7557875712 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+16)-1-1 := by
    have expansion : 8*(8*(72*R+16)-1-1) = 4608*R + 1008 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 1008 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+16)-2*(8*(72*R+16)-1) := by
    have expansion : 4*(T 8 8 (72*R+16)-2*(8*(72*R+16)-1)) = 13824*R + 3080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 3080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤2048*R+429 := by
    have expansion : 8*(2048*R+429) = 16384*R + 3432 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤16384*R + 3432 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+16) 2-2-2*(2048*R+429) := by
    have expansion : 4*(Y 8 8 (72*R+16) 2-2-2*(2048*R+429)) = 57344*R + 12944 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤57344*R + 12944 := by positivity
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

theorem residue_submask_19 (R : ℕ) : Submask 1 (2048*R+429) := by
  exact submask_high_block 11 R 429 1 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_20 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 0) = 212336640*R^2 + 186181632*R + 40804208 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤212336640*R^2 + 186181632*R + 40804208 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+32) 2 0-1-(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+32) 2 0-1-(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 0)) = 467140608*R^2 + 418977792*R + 93937872 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤467140608*R^2 + 418977792*R + 93937872 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 0) = 594542592*R^2 + 523643904*R + 115289824 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤594542592*R^2 + 523643904*R + 115289824 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+32) 2 0-1-(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+32) 2 0-1-(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 0)) = 84934656*R^2 + 81515520*R + 19452256 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 81515520*R + 19452256 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 1) = 316145664*R^2 + 281168896*R + 62514992 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤316145664*R^2 + 281168896*R + 62514992 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+32) 2 1-1-(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+32) 2 1-1-(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 1)) = 5119672320*R^2 + 4551001088*R + 1011374288 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5119672320*R^2 + 4551001088*R + 1011374288 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 1) = 783286272*R^2 + 697068544*R + 155084592 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤783286272*R^2 + 697068544*R + 155084592 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+32) 2 1-1-(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+32) 2 1-1-(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 1)) = 10088349696*R^2 + 8967271424*R + 1992693968 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10088349696*R^2 + 8967271424*R + 1992693968 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 2) = 10489430016*R^2 + 9324592128*R + 2072276992 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10489430016*R^2 + 9324592128*R + 2072276992 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+32) 2 2-1-(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+32) 2 2-1-(oldEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) 2)) = 391378894848*R^3 + 511434031104*R^2 + 222679286784*R + 32304304128 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 511434031104*R^2 + 222679286784*R + 32304304128 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 2) = 20978860032*R^2 + 18649193472*R + 4144558080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤20978860032*R^2 + 18649193472*R + 4144558080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+32) 2 2-1-(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+32) 2 2-1-(newEnds 8 8 (72*R+32) 2 (8*(72*R+32)-1) 1 (2048*R+883) true 2)) = 782757789696*R^3 + 1022783127552*R^2 + 445282919424*R + 64591761408 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤782757789696*R^3 + 1022783127552*R^2 + 445282919424*R + 64591761408 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+32)-1-1 := by
    have expansion : 8*(8*(72*R+32)-1-1) = 4608*R + 2032 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 2032 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+32)-2*(8*(72*R+32)-1) := by
    have expansion : 4*(T 8 8 (72*R+32)-2*(8*(72*R+32)-1)) = 13824*R + 6152 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 6152 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤2048*R+883 := by
    have expansion : 8*(2048*R+883) = 16384*R + 7064 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤16384*R + 7064 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+32) 2-2-2*(2048*R+883) := by
    have expansion : 4*(Y 8 8 (72*R+32) 2-2-2*(2048*R+883)) = 57344*R + 25696 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤57344*R + 25696 := by positivity
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

theorem residue_submask_20 (R : ℕ) : Submask 1 (2048*R+883) := by
  exact submask_high_block 11 R 883 1 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_21 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 0) = 212336640*R^2 + 374925312*R + 165494640 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤212336640*R^2 + 374925312*R + 165494640 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+64) 2 0-1-(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+64) 2 0-1-(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 0)) = 467140608*R^2 + 834213888*R + 372424912 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤467140608*R^2 + 834213888*R + 372424912 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 0) = 594542592*R^2 + 1052126208*R + 465460960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤594542592*R^2 + 1052126208*R + 465460960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+64) 2 0-1-(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+64) 2 0-1-(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 0)) = 84934656*R^2 + 157012992*R + 72458592 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 157012992*R + 72458592 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 1) = 231211008*R^2 + 411190272*R + 182816784 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤231211008*R^2 + 411190272*R + 182816784 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+64) 2 1-1-(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+64) 2 1-1-(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 1)) = 5204606976*R^2 + 9252817920*R + 4112445424 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5204606976*R^2 + 9252817920*R + 4112445424 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 1) = 613416960*R^2 + 1091331072*R + 485396496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤613416960*R^2 + 1091331072*R + 485396496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+64) 2 1-1-(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+64) 2 1-1-(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 1)) = 10258219008*R^2 + 18236685312*R + 8105127920 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10258219008*R^2 + 18236685312*R + 8105127920 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 2) = 10489430016*R^2 + 18648529920*R + 8288526336 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10489430016*R^2 + 18648529920*R + 8288526336 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+64) 2 2-1-(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+64) 2 2-1-(oldEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) 2)) = 391378894848*R^3 + 1033272557568*R^2 + 909215548416*R + 266656620544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 1033272557568*R^2 + 909215548416*R + 266656620544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 2) = 20978860032*R^2 + 37297069056*R + 16577060864 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤20978860032*R^2 + 37297069056*R + 16577060864 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+64) 2 2-1-(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+64) 2 2-1-(newEnds 8 8 (72*R+64) 2 (8*(72*R+64)-1) 1 (2048*R+1793) true 2)) = 782757789696*R^3 + 2066460180480*R^2 + 1818279945216*R + 533245992960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤782757789696*R^3 + 2066460180480*R^2 + 1818279945216*R + 533245992960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+64)-1-1 := by
    have expansion : 8*(8*(72*R+64)-1-1) = 4608*R + 4080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 4080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+64)-2*(8*(72*R+64)-1) := by
    have expansion : 4*(T 8 8 (72*R+64)-2*(8*(72*R+64)-1)) = 13824*R + 12296 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 12296 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤2048*R+1793 := by
    have expansion : 8*(2048*R+1793) = 16384*R + 14344 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤16384*R + 14344 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+64) 2-2-2*(2048*R+1793) := by
    have expansion : 4*(Y 8 8 (72*R+64) 2-2-2*(2048*R+1793)) = 57344*R + 51184 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤57344*R + 51184 := by positivity
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

theorem residue_submask_21 (R : ℕ) : Submask 1 (2048*R+1793) := by
  exact submask_high_block 11 R 1793 1 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_22 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 0) = 212336640*R^2 + 327739392*R + 126457712 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤212336640*R^2 + 327739392*R + 126457712 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+56) 2 0-1-(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+56) 2 0-1-(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 0)) = 467140608*R^2 + 730404864*R + 285501648 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤467140608*R^2 + 730404864*R + 285501648 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 0) = 594542592*R^2 + 920005632*R + 355898080 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤594542592*R^2 + 920005632*R + 355898080 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+56) 2 0-1-(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+56) 2 0-1-(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 0)) = 84934656*R^2 + 138138624*R + 56061280 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 138138624*R + 56061280 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 1) = 61341696*R^2 + 95564800*R + 37219792 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤61341696*R^2 + 95564800*R + 37219792 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+56) 2 1-1-(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+56) 2 1-1-(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 1)) = 5374476288*R^2 + 8360483840*R + 3251372592 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤5374476288*R^2 + 8360483840*R + 3251372592 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 1) = 273678336*R^2 + 426529792*R + 166186448 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤273678336*R^2 + 426529792*R + 166186448 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+56) 2 1-1-(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+56) 2 1-1-(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 1)) = 10597957632*R^2 + 16485567488*R + 6410998320 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10597957632*R^2 + 16485567488*R + 6410998320 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 2) = 10489430016*R^2 + 16317545472*R + 6345966592 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10489430016*R^2 + 16317545472*R + 6345966592 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+56) 2 2-1-(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+56) 2 2-1-(oldEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) 2)) = 391378894848*R^3 + 902812925952*R^2 + 694094939136*R + 177852251136 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 902812925952*R^2 + 694094939136*R + 177852251136 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 2) = 20978860032*R^2 + 32635100160*R + 12691940352 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤20978860032*R^2 + 32635100160*R + 12691940352 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+56) 2 2-1-(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+56) 2 2-1-(newEnds 8 8 (72*R+56) 2 (8*(72*R+56)-1) 1 (2048*R+1565) true 2)) = 782757789696*R^3 + 1805540917248*R^2 + 1388057601024*R + 355653000192 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤782757789696*R^3 + 1805540917248*R^2 + 1388057601024*R + 355653000192 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+56)-1-1 := by
    have expansion : 8*(8*(72*R+56)-1-1) = 4608*R + 3568 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 3568 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+56)-2*(8*(72*R+56)-1) := by
    have expansion : 4*(T 8 8 (72*R+56)-2*(8*(72*R+56)-1)) = 13824*R + 10760 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 10760 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤2048*R+1565 := by
    have expansion : 8*(2048*R+1565) = 16384*R + 12520 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤16384*R + 12520 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+56) 2-2-2*(2048*R+1565) := by
    have expansion : 4*(Y 8 8 (72*R+56) 2-2-2*(2048*R+1565)) = 57344*R + 44816 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤57344*R + 44816 := by positivity
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

theorem residue_submask_22 (R : ℕ) : Submask 1 (2048*R+1565) := by
  exact submask_high_block 11 R 1565 1 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

theorem residue_bounds_23 (R : ℤ) (hR : 0≤R) :
    rowBounds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true := by
  have hS1_lower : 0≤oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 0 := by
    have expansion : 8*(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 0) = 212336640*R^2 + 233367552*R + 64112496 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤212336640*R^2 + 233367552*R + 64112496 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS1_upper : 0≤oldHeads 8 8 (72*R+40) 2 0-1-(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 0) := by
    have expansion : 8*(oldHeads 8 8 (72*R+40) 2 0-1-(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 0)) = 467140608*R^2 + 522786816*R + 146258128 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤467140608*R^2 + 522786816*R + 146258128 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_lower : 0≤newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 0 := by
    have expansion : 8*(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 0) = 594542592*R^2 + 655764480*R + 180812512 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤594542592*R^2 + 655764480*R + 180812512 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT1_upper : 0≤newHeads 8 8 (72*R+40) 2 0-1-(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 0) := by
    have expansion : 8*(newHeads 8 8 (72*R+40) 2 0-1-(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 0)) = 84934656*R^2 + 100389888*R + 29558112 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤84934656*R^2 + 100389888*R + 29558112 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_lower : 0≤oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 1 := by
    have expansion : 8*(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 1) = 486014976*R^2 + 540171264*R + 150090096 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤486014976*R^2 + 540171264*R + 150090096 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS2_upper : 0≤oldHeads 8 8 (72*R+40) 2 1-1-(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 1) := by
    have expansion : 8*(oldHeads 8 8 (72*R+40) 2 1-1-(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 1)) = 4949803008*R^2 + 5499958272*R + 1527815824 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4949803008*R^2 + 5499958272*R + 1527815824 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_lower : 0≤newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 1 := by
    have expansion : 8*(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 1) = 1123024896*R^2 + 1248623616*R + 347066736 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤1123024896*R^2 + 1248623616*R + 347066736 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT2_upper : 0≤newHeads 8 8 (72*R+40) 2 1-1-(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 1) := by
    have expansion : 8*(newHeads 8 8 (72*R+40) 2 1-1-(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 1)) = 9748611072*R^2 + 10831635456*R + 3008745104 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤9748611072*R^2 + 10831635456*R + 3008745104 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_lower : 0≤oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 2 := by
    have expansion : 8*(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 2) = 10489430016*R^2 + 11655576576*R + 3237841920 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤10489430016*R^2 + 11655576576*R + 3237841920 := by positivity
    nlinarith only [expansion,nonnegative]
  have hS3_upper : 0≤oldHeads 8 8 (72*R+40) 2 2-1-(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 2) := by
    have expansion : 8*(oldHeads 8 8 (72*R+40) 2 2-1-(oldEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) 2)) = 391378894848*R^3 + 641893662720*R^2 + 350826808320*R + 63897318400 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤391378894848*R^3 + 641893662720*R^2 + 350826808320*R + 63897318400 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_lower : 0≤newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 2 := by
    have expansion : 8*(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 2) = 20978860032*R^2 + 23311162368*R + 6475688960 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤20978860032*R^2 + 23311162368*R + 6475688960 := by positivity
    nlinarith only [expansion,nonnegative]
  have hT3_upper : 0≤newHeads 8 8 (72*R+40) 2 2-1-(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 2) := by
    have expansion : 8*(newHeads 8 8 (72*R+40) 2 2-1-(newEnds 8 8 (72*R+40) 2 (8*(72*R+40)-1) 1 (2048*R+1111) true 2)) = 782757789696*R^3 + 1283702390784*R^2 + 701559088128*R + 127768335360 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤782757789696*R^3 + 1283702390784*R^2 + 701559088128*R + 127768335360 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_lower : 0≤8*(72*R+40)-1-1 := by
    have expansion : 8*(8*(72*R+40)-1-1) = 4608*R + 2544 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤4608*R + 2544 := by positivity
    nlinarith only [expansion,nonnegative]
  have hv_upper : 0≤T 8 8 (72*R+40)-2*(8*(72*R+40)-1) := by
    have expansion : 4*(T 8 8 (72*R+40)-2*(8*(72*R+40)-1)) = 13824*R + 7688 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤13824*R + 7688 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_lower : 0≤2048*R+1111 := by
    have expansion : 8*(2048*R+1111) = 16384*R + 8888 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤16384*R + 8888 := by positivity
    nlinarith only [expansion,nonnegative]
  have hM_upper : 0≤Y 8 8 (72*R+40) 2-2-2*(2048*R+1111) := by
    have expansion : 4*(Y 8 8 (72*R+40) 2-2-2*(2048*R+1111)) = 57344*R + 32064 := by
      try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
      ring
    have nonnegative : (0:ℤ)≤57344*R + 32064 := by positivity
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

theorem residue_submask_23 (R : ℕ) : Submask 1 (2048*R+1111) := by
  exact submask_high_block 11 R 1111 1 (by norm_num) (by norm_num)
    (submask_of_land _ _ (by decide))

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
