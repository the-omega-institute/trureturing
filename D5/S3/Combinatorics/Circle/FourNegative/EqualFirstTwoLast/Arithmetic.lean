/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoLast/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-arithmetic-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact coefficient certificates for both unbounded equal-first-two-last charts. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

/-! Source preparation only: no current elaboration or kernel acceptance is claimed.
The construction and symbolic certificate are caller-derived. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast

private def A (q z : ℤ) : ℤ := q*q*z+(1+q+q*q)
private def B (q : ℤ) : ℤ := q*(1+q+q*q)+1
private def L (q z : ℤ) : ℤ := q*(z*(1+q))+1+z
private def M (q z : ℤ) : ℤ := q*(q*z)+1+q+q*z
private def N (q z : ℤ) : ℤ := q*q*z*q-1
private def Bn (q : ℤ) : ℤ := 2*B q-1
private def Ln (q z : ℤ) : ℤ := 2*L q z-1-z
private def Mn (q z : ℤ) : ℤ := 2*M q z-1-q-q*z
private def Margin (seam successor : ℤ) : Prop :=
  0 ≤ 2*seam ∧ 0 ≤ successor-1-2*seam
private def UpperBounds (q z v : ℤ) : Prop :=
  Margin (L q z-v*B q) (L q z) ∧
  Margin (L q z+A q z-M q z-v*B q) (A q z) ∧
  Margin (A q z-v*B q) (M q z) ∧ Margin 0 (B q) ∧
  Margin (Ln q z-v*Bn q) (Ln q z) ∧
  Margin (Ln q z+2*A q z-Mn q z-v*Bn q) (A q z) ∧
  Margin (2*A q z-v*Bn q) (Mn q z) ∧ Margin 0 (Bn q)
private def LowerBounds (q z p : ℤ) : Prop :=
  Margin (A q z-M q z) (A q z) ∧
  Margin (A q z-L q z) (M q z) ∧
  Margin (B q-L q z-p*A q z) (B q) ∧ Margin 0 (L q z) ∧
  Margin (2*A q z-Mn q z) (A q z) ∧
  Margin (2*A q z-Ln q z) (Mn q z) ∧
  Margin (Bn q-Ln q z-2*p*A q z) (Bn q) ∧ Margin 0 (Ln q z) ∧
  0 ≤ A q z ∧ 0 ≤ N q z-A q z

set_option maxHeartbeats 2000000 in
private theorem upper_chart (q m : ℤ) (hq : 4 ≤ q) (hm : 1 ≤ m) :
    UpperBounds q (4*q*m) (3*m) := by
  obtain ⟨Q,hQ,rfl⟩ : ∃ Q : ℤ, 0 ≤ Q ∧ q=4+Q :=
    ⟨q-4,by omega,by ring⟩
  obtain ⟨H,hH,rfl⟩ : ∃ H : ℤ, 0 ≤ H ∧ m=1+H :=
    ⟨m-1,by omega,by ring⟩
  have old_seam_0 : 0 ≤ 2*(L (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*B (4+Q)) := by
    calc
      _ = 164 + 162*H + 114*Q + 114*Q*H + 26*Q^2 + 26*Q^2*H + 2*Q^3 + 2*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_peak_slack_0 : 0 ≤ L (4+Q) (4*(4+Q)*(1+H))-1-2*(L (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*B (4+Q)) := by
    calc
      _ = 172 + 174*H + 114*Q + 114*Q*H + 26*Q^2 + 26*Q^2*H + 2*Q^3 + 2*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_0 : 0 ≤ 2*(Ln (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*Bn (4+Q)) := by
    calc
      _ = 300 + 298*H + 220*Q + 220*Q*H + 52*Q^2 + 52*Q^2*H + 4*Q^3 + 4*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_peak_slack_0 : 0 ≤ Ln (4+Q) (4*(4+Q)*(1+H))-1-2*(Ln (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*Bn (4+Q)) := by
    calc
      _ = 356 + 358*H + 232*Q + 232*Q*H + 52*Q^2 + 52*Q^2*H + 4*Q^3 + 4*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_seam_1 : 0 ≤ 2*(L (4+Q) (4*(4+Q)*(1+H))+A (4+Q) (4*(4+Q)*(1+H))-M (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*B (4+Q)) := by
    calc
      _ = 68 + 34*H + 66*Q + 50*Q*H + 20*Q^2 + 18*Q^2*H + 2*Q^3 + 2*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_peak_slack_1 : 0 ≤ A (4+Q) (4*(4+Q)*(1+H))-1-2*(L (4+Q) (4*(4+Q)*(1+H))+A (4+Q) (4*(4+Q)*(1+H))-M (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*B (4+Q)) := by
    calc
      _ = 208 + 222*H + 135*Q + 142*Q*H + 29*Q^2 + 30*Q^2*H + 2*Q^3 + 2*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_1 : 0 ≤ 2*(Ln (4+Q) (4*(4+Q)*(1+H))+2*A (4+Q) (4*(4+Q)*(1+H))-Mn (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*Bn (4+Q)) := by
    calc
      _ = 246 + 170*H + 190*Q + 156*Q*H + 48*Q^2 + 44*Q^2*H + 4*Q^3 + 4*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_peak_slack_1 : 0 ≤ A (4+Q) (4*(4+Q)*(1+H))-1-2*(Ln (4+Q) (4*(4+Q)*(1+H))+2*A (4+Q) (4*(4+Q)*(1+H))-Mn (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*Bn (4+Q)) := by
    calc
      _ = 30 + 86*H + 11*Q + 36*Q*H + Q^2 + 4*Q^2*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_seam_2 : 0 ≤ 2*(A (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*B (4+Q)) := by
    calc
      _ = 44 + 2*H + 60*Q + 42*Q*H + 20*Q^2 + 18*Q^2*H + 2*Q^3 + 2*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_peak_slack_2 : 0 ≤ M (4+Q) (4*(4+Q)*(1+H))-1-2*(A (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*B (4+Q)) := by
    calc
      _ = 280 + 318*H + 165*Q + 182*Q*H + 32*Q^2 + 34*Q^2*H + 2*Q^3 + 2*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_2 : 0 ≤ 2*(2*A (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*Bn (4+Q)) := by
    calc
      _ = 94 + 10*H + 120*Q + 84*Q*H + 40*Q^2 + 36*Q^2*H + 4*Q^3 + 4*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_peak_slack_2 : 0 ≤ Mn (4+Q) (4*(4+Q)*(1+H))-1-2*(2*A (4+Q) (4*(4+Q)*(1+H))-(3*(1+H))*Bn (4+Q)) := by
    calc
      _ = 486 + 566*H + 297*Q + 332*Q*H + 60*Q^2 + 64*Q^2*H + 4*Q^3 + 4*Q^3*H := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_seam_3 : (0 : ℤ) ≤ 2*(0 : ℤ) := by norm_num
  have old_peak_slack_3 : 0 ≤ B (4+Q)-1-2*(0) := by
    calc
      _ = 84 + 57*Q + 13*Q^2 + Q^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_3 : (0 : ℤ) ≤ 2*(0 : ℤ) := by norm_num
  have new_peak_slack_3 : 0 ≤ Bn (4+Q)-1-2*(0) := by
    calc
      _ = 168 + 114*Q + 26*Q^2 + 2*Q^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  exact ⟨⟨old_seam_0,old_peak_slack_0⟩,⟨old_seam_1,old_peak_slack_1⟩,⟨old_seam_2,old_peak_slack_2⟩,⟨old_seam_3,old_peak_slack_3⟩,⟨new_seam_0,new_peak_slack_0⟩,⟨new_seam_1,new_peak_slack_1⟩,⟨new_seam_2,new_peak_slack_2⟩,⟨new_seam_3,new_peak_slack_3⟩⟩

set_option maxHeartbeats 2000000 in
private theorem lower_chart (z m : ℤ) (hz : 4 ≤ z) (hm : 2 ≤ m) :
    LowerBounds (2*z*m) z (m-1) := by
  obtain ⟨Q,hQ,rfl⟩ : ∃ Q : ℤ, 0 ≤ Q ∧ z=4+Q :=
    ⟨z-4,by omega,by ring⟩
  obtain ⟨H,hH,rfl⟩ : ∃ H : ℤ, 0 ≤ H ∧ m=2+H :=
    ⟨m-2,by omega,by ring⟩
  have old_seam_0 : 0 ≤ 2*(A (2*(4+Q)*(2+H)) (4+Q)-M (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 384 + 448*H + 128*H^2 + 192*Q + 224*Q*H + 64*Q*H^2 + 24*Q^2 + 28*Q^2*H + 8*Q^2*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_peak_slack_0 : 0 ≤ A (2*(4+Q)*(2+H)) (4+Q)-1-2*(A (2*(4+Q)*(2+H)) (4+Q)-M (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 912 + 840*H + 192*H^2 + 708*Q + 674*Q*H + 160*Q*H^2 + 184*Q^2 + 180*Q^2*H + 44*Q^2*H^2 + 16*Q^3 + 16*Q^3*H + 4*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_0 : 0 ≤ 2*(2*A (2*(4+Q)*(2+H)) (4+Q)-Mn (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 930 + 976*H + 256*H^2 + 456*Q + 484*Q*H + 128*Q*H^2 + 56*Q^2 + 60*Q^2*H + 16*Q^2*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_peak_slack_0 : 0 ≤ A (2*(4+Q)*(2+H)) (4+Q)-1-2*(2*A (2*(4+Q)*(2+H)) (4+Q)-Mn (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 366 + 312*H + 64*H^2 + 444*Q + 414*Q*H + 96*Q*H^2 + 152*Q^2 + 148*Q^2*H + 36*Q^2*H^2 + 16*Q^3 + 16*Q^3*H + 4*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_seam_1 : 0 ≤ 2*(A (2*(4+Q)*(2+H)) (4+Q)-L (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 408 + 464*H + 128*H^2 + 198*Q + 228*Q*H + 64*Q*H^2 + 24*Q^2 + 28*Q^2*H + 8*Q^2*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_peak_slack_1 : 0 ≤ M (2*(4+Q)*(2+H)) (4+Q)-1-2*(A (2*(4+Q)*(2+H)) (4+Q)-L (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 696 + 600*H + 128*H^2 + 606*Q + 558*Q*H + 128*Q*H^2 + 172*Q^2 + 166*Q^2*H + 40*Q^2*H^2 + 16*Q^3 + 16*Q^3*H + 4*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_1 : 0 ≤ 2*(2*A (2*(4+Q)*(2+H)) (4+Q)-Ln (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 826 + 928*H + 256*H^2 + 398*Q + 456*Q*H + 128*Q*H^2 + 48*Q^2 + 56*Q^2*H + 16*Q^2*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_peak_slack_1 : 0 ≤ Mn (2*(4+Q)*(2+H)) (4+Q)-1-2*(2*A (2*(4+Q)*(2+H)) (4+Q)-Ln (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 1302 + 1160*H + 256*H^2 + 1174*Q + 1098*Q*H + 256*Q*H^2 + 340*Q^2 + 330*Q^2*H + 80*Q^2*H^2 + 32*Q^3 + 32*Q^3*H + 8*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_seam_2 : 0 ≤ 2*(B (2*(4+Q)*(2+H))-L (2*(4+Q)*(2+H)) (4+Q)-((2+H)-1)*A (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 3958 + 5534*H + 2544*H^2 + 384*H^3 + 3006*Q + 4312*Q*H + 2044*Q*H^2 + 320*Q*H^3 + 760*Q^2 + 1116*Q^2*H + 544*Q^2*H^2 + 88*Q^2*H^3 + 64*Q^3 + 96*Q^3*H + 48*Q^3*H^2 + 8*Q^3*H^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_peak_slack_2 : 0 ≤ B (2*(4+Q)*(2+H))-1-2*(B (2*(4+Q)*(2+H))-L (2*(4+Q)*(2+H)) (4+Q)-((2+H)-1)*A (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 410 + 874*H + 592*H^2 + 128*H^3 + 198*Q + 426*Q*H + 292*Q*H^2 + 64*Q*H^3 + 24*Q^2 + 52*Q^2*H + 36*Q^2*H^2 + 8*Q^2*H^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_2 : 0 ≤ 2*(Bn (2*(4+Q)*(2+H))-Ln (2*(4+Q)*(2+H)) (4+Q)-2*((2+H)-1)*A (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 7924 + 11068*H + 5088*H^2 + 768*H^3 + 6014*Q + 8624*Q*H + 4088*Q*H^2 + 640*Q*H^3 + 1520*Q^2 + 2232*Q^2*H + 1088*Q^2*H^2 + 176*Q^2*H^3 + 128*Q^3 + 192*Q^3*H + 96*Q^3*H^2 + 16*Q^3*H^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_peak_slack_2 : 0 ≤ Bn (2*(4+Q)*(2+H))-1-2*(Bn (2*(4+Q)*(2+H))-Ln (2*(4+Q)*(2+H)) (4+Q)-2*((2+H)-1)*A (2*(4+Q)*(2+H)) (4+Q)) := by
    calc
      _ = 812 + 1748*H + 1184*H^2 + 256*H^3 + 394*Q + 852*Q*H + 584*Q*H^2 + 128*Q*H^3 + 48*Q^2 + 104*Q^2*H + 72*Q^2*H^2 + 16*Q^2*H^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have old_seam_3 : (0 : ℤ) ≤ 2*(0 : ℤ) := by norm_num
  have old_peak_slack_3 : 0 ≤ L (2*(4+Q)*(2+H)) (4+Q)-1-2*(0) := by
    calc
      _ = 1092 + 1056*H + 256*H^2 + 801*Q + 784*Q*H + 192*Q*H^2 + 196*Q^2 + 194*Q^2*H + 48*Q^2*H^2 + 16*Q^3 + 16*Q^3*H + 4*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have new_seam_3 : (0 : ℤ) ≤ 2*(0 : ℤ) := by norm_num
  have new_peak_slack_3 : 0 ≤ Ln (2*(4+Q)*(2+H)) (4+Q)-1-2*(0) := by
    calc
      _ = 2180 + 2112*H + 512*H^2 + 1601*Q + 1568*Q*H + 384*Q*H^2 + 392*Q^2 + 388*Q^2*H + 96*Q^2*H^2 + 32*Q^3 + 32*Q^3*H + 8*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have fresh_nonnegative : 0 ≤ A (2*(4+Q)*(2+H)) (4+Q) := by
    calc
      _ = 1297 + 1288*H + 320*H^2 + 900*Q + 898*Q*H + 224*Q*H^2 + 208*Q^2 + 208*Q^2*H + 52*Q^2*H^2 + 16*Q^3 + 16*Q^3*H + 4*Q^3*H^2 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  have fresh_upper : 0 ≤ N (2*(4+Q)*(2+H)) (4+Q)-A (2*(4+Q)*(2+H)) (4+Q) := by
    calc
      _ = 15086 + 23288*H + 11968*H^2 + 2048*H^3 + 15484*Q + 23678*Q*H + 12064*Q*H^2 + 2048*Q*H^3 + 5936*Q^2 + 9008*Q^2*H + 4556*Q^2*H^2 + 768*Q^2*H^3 + 1008*Q^3 + 1520*Q^3*H + 764*Q^3*H^2 + 128*Q^3*H^3 + 64*Q^4 + 96*Q^4*H + 48*Q^4*H^2 + 8*Q^4*H^3 := by
        dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
      _ ≥ 0 := by positivity
  exact ⟨⟨old_seam_0,old_peak_slack_0⟩,⟨old_seam_1,old_peak_slack_1⟩,⟨old_seam_2,old_peak_slack_2⟩,⟨old_seam_3,old_peak_slack_3⟩,⟨new_seam_0,new_peak_slack_0⟩,⟨new_seam_1,new_peak_slack_1⟩,⟨new_seam_2,new_peak_slack_2⟩,⟨new_seam_3,new_peak_slack_3⟩,fresh_nonnegative,fresh_upper⟩

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast
