/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SmallAAllHCertificates
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: 340 exact polynomial identities for twenty universal physical window families. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHData

/-! Each identity is proved by ring and its nonnegative polynomial
by positivity, for arbitrary nonnegative integer R and U. No finite evaluation
proves an infinite claim. All heads are the actual old/new physical heads. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH

private theorem residue_certificate_0 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true ∧ ((1+U)*5)<((1+U)*(2048*R+205)) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 0 := by
    have he : (oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 0 : ℤ) = 128182 + 127626*U + 2628288*R + 2623104*R*U + 13271040*R^2 + 13271040*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 (72*R+8) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 0) := by
    have he : (oldHeads 8 4 (72*R+8) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 0) : ℤ) = 936786 + 937334*U + 16393536*R + 16398720*R*U + 71663616*R^2 + 71663616*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 0 := by
    have he : (newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 0 : ℤ) = 521956 + 520842*U + 10006272*R + 9995904*R*U + 47775744*R^2 + 47775744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 (72*R+8) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 0) := by
    have he : (newHeads 8 4 (72*R+8) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 0) : ℤ) = 543012 + 544118*U + 9015552*R + 9025920*R*U + 37158912*R^2 + 37158912*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 1 := by
    have he : (oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 1 : ℤ) = 1501722 + 1497114*U + 27049088*R + 27007616*R*U + 121798656*R^2 + 121798656*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 (72*R+8) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 1) := by
    have he : (oldHeads 8 4 (72*R+8) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 1) : ℤ) = 2694886 + 2697190*U + 48469120*R + 48489856*R*U + 217939968*R^2 + 217939968*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 1 := by
    have he : (newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 1 : ℤ) = 3243034 + 3233818*U + 58351232*R + 58268288*R*U + 262471680*R^2 + 262471680*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 (72*R+8) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 1) := by
    have he : (newHeads 8 4 (72*R+8) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 1) : ℤ) = 5150182 + 5154790*U + 92685184*R + 92726656*R*U + 417005568*R^2 + 417005568*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 2 := by
    have he : (oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 2 : ℤ) = 8098176 + 8388608*U + 145726848*R + 150994944*R*U + 655589376*R^2 + 679477248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 (72*R+8) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 2) := by
    have he : (oldHeads 8 4 (72*R+8) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) 2) : ℤ) = 25589376 + 25298944*U + 762620544*R + 757352448*R*U + 7508754432*R^2 + 7484866560*R^2*U + 24461180928*R^3 + 24461180928*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 2 := by
    have he : (newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 2 : ℤ) = 16196480 + 16777216*U + 291454848*R + 301989888*R*U + 1311178752*R^2 + 1358954496*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 (72*R+8) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 2) := by
    have he : (newHeads 8 4 (72*R+8) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+8) (4*(1+U)) (4*(72*R+8)-1) ((1+U)*5) ((1+U)*(2048*R+205)) true 2) : ℤ) = 51045504 + 50464768*U + 1522862208*R + 1512327168*R*U + 15006892032*R^2 + 14959116288*R^2*U + 48922361856*R^3 + 48922361856*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(4*(72*R+8)-1)-1 := by
    have he : ((4*(72*R+8)-1)-1 : ℤ) = 30 + 288*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 (72*R+8)-2*(4*(72*R+8)-1) := by
    have he : (T 8 4 (72*R+8)-2*(4*(72*R+8)-1) : ℤ) = 194 + 1728*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(2048*R+205)) := by
    have he : (((1+U)*(2048*R+205)) : ℤ) = 205 + 205*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 (72*R+8) (4*(1+U))-2-2*((1+U)*(2048*R+205)) := by
    have he : (Y 8 4 (72*R+8) (4*(1+U))-2-2*((1+U)*(2048*R+205)) : ℤ) = 1636 + 1638*U + 14336*R + 14336*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(2048*R+205))-((1+U)*5)-1 := by
    have he : (((1+U)*(2048*R+205))-((1+U)*5)-1 : ℤ) = 199 + 200*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_1 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true ∧ ((1+U)*5)<((1+U)*(2048*R+429)) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 0 := by
    have he : (oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 0 : ℤ) = 584054 + 582922*U + 5577408*R + 5572224*R*U + 13271040*R^2 + 13271040*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 (72*R+16) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 0) := by
    have he : (oldHeads 8 4 (72*R+16) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 0) : ℤ) = 3643026 + 3644150*U + 32318784*R + 32323968*R*U + 71663616*R^2 + 71663616*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 0 := by
    have he : (newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 0 : ℤ) = 2223588 + 2221322*U + 20623104*R + 20612736*R*U + 47775744*R^2 + 47775744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 (72*R+16) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 0) := by
    have he : (newHeads 8 4 (72*R+16) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 0) : ℤ) = 2003492 + 2005750*U + 17273088*R + 17283456*R*U + 37158912*R^2 + 37158912*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 1 := by
    have he : (oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 1 : ℤ) = 1815642 + 1806426*U + 16362624*R + 16321152*R*U + 36864000*R^2 + 36864000*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 (72*R+16) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 1) := by
    have he : (oldHeads 8 4 (72*R+16) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 1) : ℤ) = 14966182 + 14970790*U + 134653056*R + 134673792*R*U + 302874624*R^2 + 302874624*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 1 := by
    have he : (newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 1 : ℤ) = 4577370 + 4558938*U + 41176704*R + 41093760*R*U + 92602368*R^2 + 92602368*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 (72*R+16) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 1) := by
    have he : (newHeads 8 4 (72*R+16) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 1) : ℤ) = 28986278 + 28995494*U + 260854656*R + 260896128*R*U + 586874880*R^2 + 586874880*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 2 := by
    have he : (oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 2 : ℤ) = 32383744 + 33554432*U + 291413376*R + 301989888*R*U + 655589376*R^2 + 679477248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 (72*R+16) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 2) := by
    have he : (oldHeads 8 4 (72*R+16) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) 2) : ℤ) = 236580096 + 235409408*U + 3337202304*R + 3326625792*R*U + 15662481408*R^2 + 15638593536*R^2*U + 24461180928*R^3 + 24461180928*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 2 := by
    have he : (newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 2 : ℤ) = 64767744 + 67108864*U + 582827904*R + 603979776*R*U + 1311178752*R^2 + 1358954496*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 (72*R+16) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 2) := by
    have he : (newHeads 8 4 (72*R+16) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+16) (4*(1+U)) (4*(72*R+16)-1) ((1+U)*5) ((1+U)*(2048*R+429)) true 2) : ℤ) = 472631552 + 470290432*U + 6669666432*R + 6648514560*R*U + 31314345984*R^2 + 31266570240*R^2*U + 48922361856*R^3 + 48922361856*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(4*(72*R+16)-1)-1 := by
    have he : ((4*(72*R+16)-1)-1 : ℤ) = 62 + 288*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 (72*R+16)-2*(4*(72*R+16)-1) := by
    have he : (T 8 4 (72*R+16)-2*(4*(72*R+16)-1) : ℤ) = 386 + 1728*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(2048*R+429)) := by
    have he : (((1+U)*(2048*R+429)) : ℤ) = 429 + 429*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 (72*R+16) (4*(1+U))-2-2*((1+U)*(2048*R+429)) := by
    have he : (Y 8 4 (72*R+16) (4*(1+U))-2-2*((1+U)*(2048*R+429)) : ℤ) = 3236 + 3238*U + 14336*R + 14336*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(2048*R+429))-((1+U)*5)-1 := by
    have he : (((1+U)*(2048*R+429))-((1+U)*5)-1 : ℤ) = 423 + 424*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_2 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true ∧ ((1+U)*5)<((1+U)*(2048*R+885)) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 0 := by
    have he : (oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 0 : ℤ) = 2478838 + 2476554*U + 11475648*R + 11470464*R*U + 13271040*R^2 + 13271040*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 (72*R+32) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 0) := by
    have he : (oldHeads 8 4 (72*R+32) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 0) : ℤ) = 14363922 + 14366198*U + 64169280*R + 64174464*R*U + 71663616*R^2 + 71663616*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 0 := by
    have he : (newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 0 : ℤ) = 9165796 + 9161226*U + 41856768*R + 41846400*R*U + 47775744*R^2 + 47775744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 (72*R+32) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 0) := by
    have he : (newHeads 8 4 (72*R+32) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 0) : ℤ) = 7676964 + 7681526*U + 33788160*R + 33798528*R*U + 37158912*R^2 + 37158912*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 1 := by
    have he : (oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 1 : ℤ) = 11466986 + 11448554*U + 51622016*R + 51580544*R*U + 58097664*R^2 + 58097664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 (72*R+32) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 1) := by
    have he : (oldHeads 8 4 (72*R+32) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 1) : ℤ) = 55651094 + 55660310*U + 250388608*R + 250409344*R*U + 281640960*R^2 + 281640960*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 1 := by
    have he : (newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 1 : ℤ) = 26689770 + 26652906*U + 120083072*R + 120000128*R*U + 135069696*R^2 + 135069696*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 (72*R+32) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 1) := by
    have he : (newHeads 8 4 (72*R+32) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 1) : ℤ) = 107546390 + 107564822*U + 483938176*R + 483979648*R*U + 544407552*R^2 + 544407552*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 2 := by
    have he : (oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 2 : ℤ) = 129517056 + 134217728*U + 582786432*R + 603979776*R*U + 655589376*R^2 + 679477248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 (72*R+32) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 2) := by
    have he : (oldHeads 8 4 (72*R+32) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) 2) : ℤ) = 2020071936 + 2015371264*U + 13922183808*R + 13900990464*R*U + 31969935360*R^2 + 31946047488*R^2*U + 24461180928*R^3 + 24461180928*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 2 := by
    have he : (newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 2 : ℤ) = 259034624 + 268435456*U + 1165574016*R + 1207959552*R*U + 1311178752*R^2 + 1358954496*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 (72*R+32) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 2) := by
    have he : (newHeads 8 4 (72*R+32) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+32) (4*(1+U)) (4*(72*R+32)-1) ((1+U)*5) ((1+U)*(2048*R+885)) true 2) : ℤ) = 4038038016 + 4028637184*U + 27834910848*R + 27792525312*R*U + 63929253888*R^2 + 63881478144*R^2*U + 48922361856*R^3 + 48922361856*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(4*(72*R+32)-1)-1 := by
    have he : ((4*(72*R+32)-1)-1 : ℤ) = 126 + 288*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 (72*R+32)-2*(4*(72*R+32)-1) := by
    have he : (T 8 4 (72*R+32)-2*(4*(72*R+32)-1) : ℤ) = 770 + 1728*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(2048*R+885)) := by
    have he : (((1+U)*(2048*R+885)) : ℤ) = 885 + 885*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 (72*R+32) (4*(1+U))-2-2*((1+U)*(2048*R+885)) := by
    have he : (Y 8 4 (72*R+32) (4*(1+U))-2-2*((1+U)*(2048*R+885)) : ℤ) = 6420 + 6422*U + 14336*R + 14336*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(2048*R+885))-((1+U)*5)-1 := by
    have he : (((1+U)*(2048*R+885))-((1+U)*5)-1 : ℤ) = 879 + 880*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_3 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true ∧ ((1+U)*5)<((1+U)*(2048*R+1797)) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 0 := by
    have he : (oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 0 : ℤ) = 10200566 + 10195978*U + 23272128*R + 23266944*R*U + 13271040*R^2 + 13271040*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 (72*R+64) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 0) := by
    have he : (oldHeads 8 4 (72*R+64) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 0) : ℤ) = 57039378 + 57043958*U + 127870272*R + 127875456*R*U + 71663616*R^2 + 71663616*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 0 := by
    have he : (newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 0 : ℤ) = 37205988 + 37196810*U + 84324096*R + 84313728*R*U + 47775744*R^2 + 47775744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 (72*R+64) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 0) := by
    have he : (newHeads 8 4 (72*R+64) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 0) : ℤ) = 30033956 + 30043126*U + 66818304*R + 66828672*R*U + 37158912*R^2 + 37158912*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 1 := by
    have he : (oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 1 : ℤ) = 79442442 + 79405578*U + 178763904*R + 178722432*R*U + 100564992*R^2 + 100564992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 (72*R+64) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 1) := by
    have he : (oldHeads 8 4 (72*R+64) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 1) : ℤ) = 189011446 + 189029878*U + 425236608*R + 425257344*R*U + 239173632*R^2 + 239173632*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 1 := by
    have he : (newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 1 : ℤ) = 173851146 + 173777418*U + 391142016*R + 391059072*R*U + 220004352*R^2 + 220004352*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 (72*R+64) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 1) := by
    have he : (newHeads 8 4 (72*R+64) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 1) : ℤ) = 363056630 + 363093494*U + 816859008*R + 816900480*R*U + 459472896*R^2 + 459472896*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 2 := by
    have he : (oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 2 : ℤ) = 518032384 + 536870912*U + 1165532544*R + 1207959552*R*U + 655589376*R^2 + 679477248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 (72*R+64) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 2) := by
    have he : (oldHeads 8 4 (72*R+64) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) 2) : ℤ) = 16670241792 + 16651403264*U + 56835418752*R + 56792991744*R*U + 64584843264*R^2 + 64560955392*R^2*U + 24461180928*R^3 + 24461180928*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 2 := by
    have he : (newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 2 : ℤ) = 1036065792 + 1073741824*U + 2331066240*R + 2415919104*R*U + 1311178752*R^2 + 1358954496*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 (72*R+64) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 2) := by
    have he : (newHeads 8 4 (72*R+64) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+64) (4*(1+U)) (4*(72*R+64)-1) ((1+U)*5) ((1+U)*(2048*R+1797)) true 2) : ℤ) = 33332077568 + 33294401536*U + 113651943552*R + 113567090688*R*U + 129159069696*R^2 + 129111293952*R^2*U + 48922361856*R^3 + 48922361856*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(4*(72*R+64)-1)-1 := by
    have he : ((4*(72*R+64)-1)-1 : ℤ) = 254 + 288*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 (72*R+64)-2*(4*(72*R+64)-1) := by
    have he : (T 8 4 (72*R+64)-2*(4*(72*R+64)-1) : ℤ) = 1538 + 1728*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(2048*R+1797)) := by
    have he : (((1+U)*(2048*R+1797)) : ℤ) = 1797 + 1797*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 (72*R+64) (4*(1+U))-2-2*((1+U)*(2048*R+1797)) := by
    have he : (Y 8 4 (72*R+64) (4*(1+U))-2-2*((1+U)*(2048*R+1797)) : ℤ) = 12788 + 12790*U + 14336*R + 14336*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(2048*R+1797))-((1+U)*5)-1 := by
    have he : (((1+U)*(2048*R+1797))-((1+U)*5)-1 : ℤ) = 1791 + 1792*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_4 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true ∧ ((1+U)*5)<((1+U)*(2048*R+1567)) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 0 := by
    have he : (oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 0 : ℤ) = 7778614 + 7774602*U + 20323008*R + 20317824*R*U + 13271040*R^2 + 13271040*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 (72*R+56) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 0) := by
    have he : (oldHeads 8 4 (72*R+56) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 0) : ℤ) = 43716306 + 43720310*U + 111945024*R + 111950208*R*U + 71663616*R^2 + 71663616*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 0 := by
    have he : (newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 0 : ℤ) = 28426468 + 28418442*U + 73707264*R + 73696896*R*U + 47775744*R^2 + 47775744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 (72*R+56) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 0) := by
    have he : (newHeads 8 4 (72*R+56) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 0) : ℤ) = 23068452 + 23076470*U + 58560768*R + 58571136*R*U + 37158912*R^2 + 37158912*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 1 := by
    have he : (oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 1 : ℤ) = 25495230 + 25462974*U + 65580416*R + 65538944*R*U + 42172416*R^2 + 42172416*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 (72*R+56) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 1) := by
    have he : (oldHeads 8 4 (72*R+56) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 1) : ℤ) = 180041794 + 180057922*U + 462922624*R + 462943360*R*U + 297566208*R^2 + 297566208*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 1 := by
    have he : (newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 1 : ℤ) = 62457022 + 62392510*U + 160583552*R + 160500608*R*U + 103219200*R^2 + 103219200*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 (72*R+56) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 1) := by
    have he : (newHeads 8 4 (72*R+56) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 1) : ℤ) = 348617026 + 348649282*U + 896422528*R + 896464000*R*U + 576258048*R^2 + 576258048*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 2 := by
    have he : (oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 2 : ℤ) = 396622464 + 411041792*U + 1019846016*R + 1056964608*R*U + 655589376*R^2 + 679477248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 (72*R+56) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 2) := by
    have he : (oldHeads 8 4 (72*R+56) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) 2) : ℤ) = 11118984576 + 11104565248*U + 43389201024*R + 43352082432*R*U + 56431116288*R^2 + 56407228416*R^2*U + 24461180928*R^3 + 24461180928*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 2 := by
    have he : (newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 2 : ℤ) = 793245824 + 822083584*U + 2039693184*R + 2113929216*R*U + 1311178752*R^2 + 1358954496*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 (72*R+56) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 2) := by
    have he : (newHeads 8 4 (72*R+56) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+56) (4*(1+U)) (4*(72*R+56)-1) ((1+U)*5) ((1+U)*(2048*R+1567)) true 2) : ℤ) = 22231531392 + 22202693632*U + 86761867392*R + 86687631360*R*U + 112851615744*R^2 + 112803840000*R^2*U + 48922361856*R^3 + 48922361856*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(4*(72*R+56)-1)-1 := by
    have he : ((4*(72*R+56)-1)-1 : ℤ) = 222 + 288*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 (72*R+56)-2*(4*(72*R+56)-1) := by
    have he : (T 8 4 (72*R+56)-2*(4*(72*R+56)-1) : ℤ) = 1346 + 1728*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(2048*R+1567)) := by
    have he : (((1+U)*(2048*R+1567)) : ℤ) = 1567 + 1567*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 (72*R+56) (4*(1+U))-2-2*((1+U)*(2048*R+1567)) := by
    have he : (Y 8 4 (72*R+56) (4*(1+U))-2-2*((1+U)*(2048*R+1567)) : ℤ) = 11200 + 11202*U + 14336*R + 14336*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(2048*R+1567))-((1+U)*5)-1 := by
    have he : (((1+U)*(2048*R+1567))-((1+U)*5)-1 : ℤ) = 1561 + 1562*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_5 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true ∧ ((1+U)*5)<((1+U)*(2048*R+1111)) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 0 := by
    have he : (oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 0 : ℤ) = 3917750 + 3914890*U + 14424768*R + 14419584*R*U + 13271040*R^2 + 13271040*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 (72*R+40) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 0) := by
    have he : (oldHeads 8 4 (72*R+40) (4*(1+U)) 0-1-(oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 0) : ℤ) = 22378578 + 22381430*U + 80094528*R + 80099712*R*U + 71663616*R^2 + 71663616*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 0 := by
    have he : (newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 0 : ℤ) = 14406372 + 14400650*U + 52473600*R + 52463232*R*U + 47775744*R^2 + 47775744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 (72*R+40) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 0) := by
    have he : (newHeads 8 4 (72*R+40) (4*(1+U)) 0-1-(newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 0) : ℤ) = 11889956 + 11895670*U + 42045696*R + 42056064*R*U + 37158912*R^2 + 37158912*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 1 := by
    have he : (oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 1 : ℤ) = 6450222 + 6427182*U + 23243136*R + 23201664*R*U + 20938752*R^2 + 20938752*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 (72*R+40) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 1) := by
    have he : (oldHeads 8 4 (72*R+40) (4*(1+U)) 1-1-(oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 1) : ℤ) = 98418898 + 98430418*U + 354264960*R + 354285696*R*U + 318799872*R^2 + 318799872*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 1 := by
    have he : (newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 1 : ℤ) = 18761262 + 18715182*U + 67521408*R + 67438464*R*U + 60751872*R^2 + 60751872*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 (72*R+40) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 1) := by
    have he : (newHeads 8 4 (72*R+40) (4*(1+U)) 1-1-(newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 1) : ℤ) = 190976978 + 191000018*U + 687494784*R + 687536256*R*U + 618725376*R^2 + 618725376*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 2 := by
    have he : (oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 2 : ℤ) = 202364800 + 209715200*U + 728472960*R + 754974720*R*U + 655589376*R^2 + 679477248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 (72*R+40) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 2) := by
    have he : (oldHeads 8 4 (72*R+40) (4*(1+U)) 2-1-(oldEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) 2) : ℤ) = 3995226240 + 3987875840*U + 21932583552*R + 21906081792*R*U + 40123662336*R^2 + 40099774464*R^2*U + 24461180928*R^3 + 24461180928*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 2 := by
    have he : (newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 2 : ℤ) = 404730240 + 419430400*U + 1456947072*R + 1509949440*R*U + 1311178752*R^2 + 1358954496*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 (72*R+40) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 2) := by
    have he : (newHeads 8 4 (72*R+40) (4*(1+U)) 2-1-(newEnds 8 4 (72*R+40) (4*(1+U)) (4*(72*R+40)-1) ((1+U)*5) ((1+U)*(2048*R+1111)) true 2) : ℤ) = 7987164800 + 7972464640*U + 43853351040*R + 43800348672*R*U + 80236707840*R^2 + 80188932096*R^2*U + 48922361856*R^3 + 48922361856*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(4*(72*R+40)-1)-1 := by
    have he : ((4*(72*R+40)-1)-1 : ℤ) = 158 + 288*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 (72*R+40)-2*(4*(72*R+40)-1) := by
    have he : (T 8 4 (72*R+40)-2*(4*(72*R+40)-1) : ℤ) = 962 + 1728*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(2048*R+1111)) := by
    have he : (((1+U)*(2048*R+1111)) : ℤ) = 1111 + 1111*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 (72*R+40) (4*(1+U))-2-2*((1+U)*(2048*R+1111)) := by
    have he : (Y 8 4 (72*R+40) (4*(1+U))-2-2*((1+U)*(2048*R+1111)) : ℤ) = 8016 + 8018*U + 14336*R + 14336*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(2048*R+1111))-((1+U)*5)-1 := by
    have he : (((1+U)*(2048*R+1111))-((1+U)*5)-1 : ℤ) = 1105 + 1106*U + 2048*R + 2048*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_6 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true ∧ ((1+U)*2)<((1+U)*(4096*R+402)) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 0 := by
    have he : (oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 0 : ℤ) = 583024 + 581892*U + 11145600*R + 11135232*R*U + 53084160*R^2 + 53084160*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 (72*R+8) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 0) := by
    have he : (oldHeads 8 8 (72*R+8) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 0) : ℤ) = 1546904 + 1548028*U + 26898048*R + 26908416*R*U + 116785152*R^2 + 116785152*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 0 := by
    have he : (newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 0 : ℤ) = 1698270 + 1696004*U + 31799808*R + 31779072*R*U + 148635648*R^2 + 148635648*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 (72*R+8) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 0) := by
    have he : (newHeads 8 8 (72*R+8) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 0) : ℤ) = 431658 + 433916*U + 6243840*R + 6264576*R*U + 21233664*R^2 + 21233664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 1 := by
    have he : (oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 1 : ℤ) = 1757220 + 1748004*U + 31675648*R + 31592704*R*U + 142737408*R^2 + 142737408*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 (72*R+8) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 1) := by
    have he : (oldHeads 8 8 (72*R+8) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 1) : ℤ) = 15024604 + 15029212*U + 270355712*R + 270397184*R*U + 1216217088*R^2 + 1216217088*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 1 := by
    have he : (newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 1 : ℤ) = 3994660 + 3976228*U + 71866624*R + 71700736*R*U + 323223552*R^2 + 323223552*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 (72*R+8) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 1) := by
    have he : (newHeads 8 8 (72*R+8) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 1) : ℤ) = 29568988 + 29578204*U + 532196096*R + 532279040*R*U + 2394685440*R^2 + 2394685440*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 2 := by
    have he : (oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 2 : ℤ) = 32973696 + 33554432*U + 593444736*R + 603979776*R*U + 2670133248*R^2 + 2717908992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 (72*R+8) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 2) := by
    have he : (oldHeads 8 8 (72*R+8) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) 2) : ℤ) = 101510272 + 100929536*U + 3035189376*R + 3024654336*R*U + 29966008320*R^2 + 29918232576*R^2*U + 97844723712*R^3 + 97844723712*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 2 := by
    have he : (newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 2 : ℤ) = 65947520 + 67108864*U + 1186890624*R + 1207959552*R*U + 5340266496*R^2 + 5435817984*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 (72*R+8) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 2) := by
    have he : (newHeads 8 8 (72*R+8) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+8) (4*(1+U)) (8*(72*R+8)-1) ((1+U)*2) ((1+U)*(4096*R+402)) true 2) : ℤ) = 202754176 + 201592832*U + 6065622144*R + 6044553216*R*U + 59910782976*R^2 + 59815231488*R^2*U + 195689447424*R^3 + 195689447424*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(8*(72*R+8)-1)-1 := by
    have he : ((8*(72*R+8)-1)-1 : ℤ) = 62 + 576*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 (72*R+8)-2*(8*(72*R+8)-1) := by
    have he : (T 8 8 (72*R+8)-2*(8*(72*R+8)-1) : ℤ) = 386 + 3456*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(4096*R+402)) := by
    have he : (((1+U)*(4096*R+402)) : ℤ) = 402 + 402*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 (72*R+8) (4*(1+U))-2-2*((1+U)*(4096*R+402)) := by
    have he : (Y 8 8 (72*R+8) (4*(1+U))-2-2*((1+U)*(4096*R+402)) : ℤ) = 3290 + 3292*U + 28672*R + 28672*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(4096*R+402))-((1+U)*2)-1 := by
    have he : (((1+U)*(4096*R+402))-((1+U)*2)-1 : ℤ) = 399 + 400*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_7 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true ∧ ((1+U)*2)<((1+U)*(4096*R+855)) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 0 := by
    have he : (oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 0 : ℤ) = 2476784 + 2474500*U + 22942080*R + 22931712*R*U + 53084160*R^2 + 53084160*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 (72*R+16) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 0) := by
    have he : (oldHeads 8 8 (72*R+16) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 0) : ℤ) = 5977368 + 5979644*U + 52850304*R + 52860672*R*U + 116785152*R^2 + 116785152*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 0 := by
    have he : (newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 0 : ℤ) = 7066590 + 7062020*U + 64829952*R + 64809216*R*U + 148635648*R^2 + 148635648*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 (72*R+16) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 0) := by
    have he : (newHeads 8 8 (72*R+16) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 0) : ℤ) = 1387562 + 1392124*U + 10962432*R + 10983168*R*U + 21233664*R^2 + 21233664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 1 := by
    have he : (oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 1 : ℤ) = 2057646 + 2039214*U + 18566016*R + 18483072*R*U + 41877504*R^2 + 41877504*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 (72*R+16) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 1) := by
    have he : (oldHeads 8 8 (72*R+16) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 1) : ℤ) = 65060434 + 65069650*U + 585455232*R + 585496704*R*U + 1317076992*R^2 + 1317076992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 1 := by
    have he : (newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 1 : ℤ) = 6008238 + 5971374*U + 54038400*R + 53872512*R*U + 121503744*R^2 + 121503744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 (72*R+16) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 1) := by
    have he : (newHeads 8 8 (72*R+16) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 1) : ℤ) = 128227922 + 128246354*U + 1154004096*R + 1154087040*R*U + 2596405248*R^2 + 2596405248*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 2 := by
    have he : (oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 2 : ℤ) = 131876608 + 134217728*U + 1186807680*R + 1207959552*R*U + 2670133248*R^2 + 2717908992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 (72*R+16) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 2) := by
    have he : (oldHeads 8 8 (72*R+16) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) 2) : ℤ) = 942921984 + 940580864*U + 13318180992*R + 13297029120*R*U + 62580916224*R^2 + 62533140480*R^2*U + 97844723712*R^3 + 97844723712*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 2 := by
    have he : (newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 2 : ℤ) = 263753472 + 268435456*U + 2373616512*R + 2415919104*R*U + 5340266496*R^2 + 5435817984*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 (72*R+16) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 2) := by
    have he : (newHeads 8 8 (72*R+16) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+16) (4*(1+U)) (8*(72*R+16)-1) ((1+U)*2) ((1+U)*(4096*R+855)) true 2) : ℤ) = 1884786944 + 1880104960*U + 26626886784*R + 26584584192*R*U + 125140598784*R^2 + 125045047296*R^2*U + 195689447424*R^3 + 195689447424*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(8*(72*R+16)-1)-1 := by
    have he : ((8*(72*R+16)-1)-1 : ℤ) = 126 + 576*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 (72*R+16)-2*(8*(72*R+16)-1) := by
    have he : (T 8 8 (72*R+16)-2*(8*(72*R+16)-1) : ℤ) = 770 + 3456*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(4096*R+855)) := by
    have he : (((1+U)*(4096*R+855)) : ℤ) = 855 + 855*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 (72*R+16) (4*(1+U))-2-2*((1+U)*(4096*R+855)) := by
    have he : (Y 8 8 (72*R+16) (4*(1+U))-2-2*((1+U)*(4096*R+855)) : ℤ) = 6480 + 6482*U + 28672*R + 28672*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(4096*R+855))-((1+U)*2)-1 := by
    have he : (((1+U)*(4096*R+855))-((1+U)*2)-1 : ℤ) = 852 + 853*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_8 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true ∧ ((1+U)*2)<((1+U)*(4096*R+1766)) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 0 := by
    have he : (oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 0 : ℤ) = 10196464 + 10191876*U + 46535040*R + 46524672*R*U + 53084160*R^2 + 53084160*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 (72*R+32) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 0) := by
    have he : (oldHeads 8 8 (72*R+32) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 0) : ℤ) = 23489048 + 23493628*U + 104754816*R + 104765184*R*U + 116785152*R^2 + 116785152*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 0 := by
    have he : (newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 0 : ℤ) = 28813278 + 28804100*U + 130890240*R + 130869504*R*U + 148635648*R^2 + 148635648*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 (72*R+32) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 0) := by
    have he : (newHeads 8 8 (72*R+32) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 0) : ℤ) = 4872234 + 4881404*U + 20399616*R + 20420352*R*U + 21233664*R^2 + 21233664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 1 := by
    have he : (oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 1 : ℤ) = 15591884 + 15555020*U + 70209280*R + 70126336*R*U + 79036416*R^2 + 79036416*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 (72*R+32) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 1) := by
    have he : (oldHeads 8 8 (72*R+32) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 1) : ℤ) = 252862004 + 252880436*U + 1137791744*R + 1137833216*R*U + 1279918080*R^2 + 1279918080*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 1 := by
    have he : (newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 1 : ℤ) = 38697420 + 38623692*U + 174101248*R + 173935360*R*U + 195821568*R^2 + 195821568*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 (72*R+32) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 1) := by
    have he : (newHeads 8 8 (72*R+32) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 1) : ℤ) = 498210356 + 498247220*U + 2241900800*R + 2241983744*R*U + 2522087424*R^2 + 2522087424*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 2 := by
    have he : (oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 2 : ℤ) = 527470080 + 536870912*U + 2373533568*R + 2415919104*R*U + 2670133248*R^2 + 2717908992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 (72*R+32) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 2) := by
    have he : (oldHeads 8 8 (72*R+32) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) 2) : ℤ) = 8066675200 + 8057274368*U + 55627436160*R + 55585050624*R*U + 127810732032*R^2 + 127762956288*R^2*U + 97844723712*R^3 + 97844723712*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 2 := by
    have he : (newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 2 : ℤ) = 1054940672 + 1073741824*U + 4747068288*R + 4831838208*R*U + 5340266496*R^2 + 5435817984*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 (72*R+32) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 2) := by
    have he : (newHeads 8 8 (72*R+32) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+32) (4*(1+U)) (8*(72*R+32)-1) ((1+U)*2) ((1+U)*(4096*R+1766)) true 2) : ℤ) = 16129139200 + 16110338048*U + 111235959936*R + 111151190016*R*U + 255600230400*R^2 + 255504678912*R^2*U + 195689447424*R^3 + 195689447424*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(8*(72*R+32)-1)-1 := by
    have he : ((8*(72*R+32)-1)-1 : ℤ) = 254 + 576*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 (72*R+32)-2*(8*(72*R+32)-1) := by
    have he : (T 8 8 (72*R+32)-2*(8*(72*R+32)-1) : ℤ) = 1538 + 3456*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(4096*R+1766)) := by
    have he : (((1+U)*(4096*R+1766)) : ℤ) = 1766 + 1766*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 (72*R+32) (4*(1+U))-2-2*((1+U)*(4096*R+1766)) := by
    have he : (Y 8 8 (72*R+32) (4*(1+U))-2-2*((1+U)*(4096*R+1766)) : ℤ) = 12850 + 12852*U + 28672*R + 28672*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(4096*R+1766))-((1+U)*2)-1 := by
    have he : (((1+U)*(4096*R+1766))-((1+U)*2)-1 : ℤ) = 1763 + 1764*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_9 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true ∧ ((1+U)*2)<((1+U)*(4096*R+3586)) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 0 := by
    have he : (oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 0 : ℤ) = 41364464 + 41355268*U + 93720960*R + 93710592*R*U + 53084160*R^2 + 53084160*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 (72*R+64) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 0) := by
    have he : (oldHeads 8 8 (72*R+64) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 0) : ℤ) = 93115416 + 93124604*U + 208563840*R + 208574208*R*U + 116785152*R^2 + 116785152*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 0 := by
    have he : (newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 0 : ℤ) = 116346846 + 116328452*U + 263010816*R + 262990080*R*U + 148635648*R^2 + 148635648*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 (72*R+64) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 0) := by
    have he : (newHeads 8 8 (72*R+64) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 0) : ℤ) = 18133034 + 18151420*U + 39273984*R + 39294720*R*U + 21233664*R^2 + 21233664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 1 := by
    have he : (oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 1 : ℤ) = 45630468 + 45556740*U + 102714624*R + 102631680*R*U + 57802752*R^2 + 57802752*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 (72*R+64) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 1) := by
    have he : (oldHeads 8 8 (72*R+64) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 1) : ℤ) = 1028148220 + 1028185084*U + 2313245952*R + 2313287424*R*U + 1301151744*R^2 + 1301151744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 1 := by
    have he : (newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 1 : ℤ) = 121201668 + 121054212*U + 272666880*R + 272500992*R*U + 153354240*R^2 + 153354240*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 (72*R+64) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 1) := by
    have he : (newHeads 8 8 (72*R+64) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 1) : ℤ) = 2026355708 + 2026429436*U + 4559254272*R + 4559337216*R*U + 2564554752*R^2 + 2564554752*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 2 := by
    have he : (oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 2 : ℤ) = 2109807616 + 2147483648*U + 4746985344*R + 4831838208*R*U + 2670133248*R^2 + 2717908992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 (72*R+64) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 2) := by
    have he : (oldHeads 8 8 (72*R+64) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) 2) : ℤ) = 66626479104 + 66588803072*U + 227219034240*R + 227134181376*R*U + 258270363648*R^2 + 258222587904*R^2*U + 97844723712*R^3 + 97844723712*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 2 := by
    have he : (newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 2 : ℤ) = 4219616256 + 4294967296*U + 9493971840*R + 9663676416*R*U + 5340266496*R^2 + 5435817984*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 (72*R+64) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 2) := by
    have he : (newHeads 8 8 (72*R+64) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+64) (4*(1+U)) (8*(72*R+64)-1) ((1+U)*2) ((1+U)*(4096*R+3586)) true 2) : ℤ) = 133236147200 + 133160796160*U + 454400281728*R + 454230577152*R*U + 516519493632*R^2 + 516423942144*R^2*U + 195689447424*R^3 + 195689447424*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(8*(72*R+64)-1)-1 := by
    have he : ((8*(72*R+64)-1)-1 : ℤ) = 510 + 576*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 (72*R+64)-2*(8*(72*R+64)-1) := by
    have he : (T 8 8 (72*R+64)-2*(8*(72*R+64)-1) : ℤ) = 3074 + 3456*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(4096*R+3586)) := by
    have he : (((1+U)*(4096*R+3586)) : ℤ) = 3586 + 3586*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 (72*R+64) (4*(1+U))-2-2*((1+U)*(4096*R+3586)) := by
    have he : (Y 8 8 (72*R+64) (4*(1+U))-2-2*((1+U)*(4096*R+3586)) : ℤ) = 25594 + 25596*U + 28672*R + 28672*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(4096*R+3586))-((1+U)*2)-1 := by
    have he : (((1+U)*(4096*R+3586))-((1+U)*2)-1 : ℤ) = 3583 + 3584*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_10 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true ∧ ((1+U)*2)<((1+U)*(4096*R+3130)) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 0 := by
    have he : (oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 0 : ℤ) = 31606384 + 31598340*U + 81924480*R + 81914112*R*U + 53084160*R^2 + 53084160*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 (72*R+56) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 0) := by
    have he : (oldHeads 8 8 (72*R+56) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 0) : ℤ) = 71383448 + 71391484*U + 182611584*R + 182621952*R*U + 116785152*R^2 + 116785152*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 0 := by
    have he : (newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 0 : ℤ) = 88958430 + 88942340*U + 229980672*R + 229959936*R*U + 148635648*R^2 + 148635648*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 (72*R+56) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 0) := by
    have he : (newHeads 8 8 (72*R+56) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 0) : ℤ) = 14031402 + 14047484*U + 34555392*R + 34576128*R*U + 21233664*R^2 + 21233664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 1 := by
    have he : (oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 1 : ℤ) = 9240436 + 9175924*U + 23808256*R + 23725312*R*U + 15335424*R^2 + 15335424*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 (72*R+56) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 1) := by
    have he : (oldHeads 8 8 (72*R+56) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 1) : ℤ) = 812875404 + 812907660*U + 2090162432*R + 2090203904*R*U + 1343619072*R^2 + 1343619072*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 1 := by
    have he : (newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 1 : ℤ) = 41417588 + 41288564*U + 106466560*R + 106300672*R*U + 68419584*R^2 + 68419584*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 (72*R+56) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 1) := by
    have he : (newHeads 8 8 (72*R+56) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 1) : ℤ) = 1602814092 + 1602878604*U + 4121474816*R + 4121557760*R*U + 2649489408*R^2 + 2649489408*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 2 := by
    have he : (oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 2 : ℤ) = 1615329408 + 1644167168*U + 4153622400*R + 4227858432*R*U + 2670133248*R^2 + 2717908992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 (72*R+56) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 2) := by
    have he : (oldHeads 8 8 (72*R+56) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) 2) : ℤ) = 44434225024 + 44405387264*U + 173449498752*R + 173375262720*R*U + 225655455744*R^2 + 225607680000*R^2*U + 97844723712*R^3 + 97844723712*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 2 := by
    have he : (newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 2 : ℤ) = 3230659712 + 3288334336*U + 8307245952*R + 8455716864*R*U + 5340266496*R^2 + 5435817984*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 (72*R+56) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 2) := by
    have he : (newHeads 8 8 (72*R+56) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+56) (4*(1+U)) (8*(72*R+56)-1) ((1+U)*2) ((1+U)*(4096*R+3130)) true 2) : ℤ) = 88855575424 + 88797900800*U + 346865929344*R + 346717458432*R*U + 451289677824*R^2 + 451194126336*R^2*U + 195689447424*R^3 + 195689447424*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(8*(72*R+56)-1)-1 := by
    have he : ((8*(72*R+56)-1)-1 : ℤ) = 446 + 576*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 (72*R+56)-2*(8*(72*R+56)-1) := by
    have he : (T 8 8 (72*R+56)-2*(8*(72*R+56)-1) : ℤ) = 2690 + 3456*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(4096*R+3130)) := by
    have he : (((1+U)*(4096*R+3130)) : ℤ) = 3130 + 3130*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 (72*R+56) (4*(1+U))-2-2*((1+U)*(4096*R+3130)) := by
    have he : (Y 8 8 (72*R+56) (4*(1+U))-2-2*((1+U)*(4096*R+3130)) : ℤ) = 22410 + 22412*U + 28672*R + 28672*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(4096*R+3130))-((1+U)*2)-1 := by
    have he : (((1+U)*(4096*R+3130))-((1+U)*2)-1 : ℤ) = 3127 + 3128*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem residue_certificate_11 (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    rowBounds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true ∧ ((1+U)*2)<((1+U)*(4096*R+2222)) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 0 := by
    have he : (oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 0 : ℤ) = 16022384 + 16016644*U + 58331520*R + 58321152*R*U + 53084160*R^2 + 53084160*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 (72*R+40) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 0) := by
    have he : (oldHeads 8 8 (72*R+40) (4*(1+U)) 0-1-(oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 0) : ℤ) = 36570264 + 36575996*U + 130707072*R + 130717440*R*U + 116785152*R^2 + 116785152*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 0 := by
    have he : (newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 0 : ℤ) = 45191646 + 45180164*U + 163920384*R + 163899648*R*U + 148635648*R^2 + 148635648*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 (72*R+40) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 0) := by
    have he : (newHeads 8 8 (72*R+40) (4*(1+U)) 0-1-(newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 0) : ℤ) = 7401002 + 7412476*U + 25118208*R + 25138944*R*U + 21233664*R^2 + 21233664*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 1 := by
    have he : (oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 1 : ℤ) = 37476444 + 37430364*U + 134959872*R + 134876928*R*U + 121503744*R^2 + 121503744*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 (72*R+40) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 1) := by
    have he : (oldHeads 8 8 (72*R+40) (4*(1+U)) 1-1-(oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 1) : ℤ) = 381976996 + 382000036*U + 1375031040*R + 1375072512*R*U + 1237450752*R^2 + 1237450752*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 1 := by
    have he : (newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 1 : ℤ) = 86674524 + 86582364*U + 311990016*R + 311824128*R*U + 280756224*R^2 + 280756224*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 (72*R+40) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 1) := by
    have he : (newHeads 8 8 (72*R+40) (4*(1+U)) 1-1-(newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 1) : ℤ) = 752232356 + 752278436*U + 2707991808*R + 2708074752*R*U + 2437152768*R^2 + 2437152768*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 2 := by
    have he : (oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 2 : ℤ) = 824160640 + 838860800*U + 2966896512*R + 3019898880*R*U + 2670133248*R^2 + 2717908992*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 (72*R+40) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 2) := by
    have he : (oldHeads 8 8 (72*R+40) (4*(1+U)) 2-1-(oldEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) 2) : ℤ) = 15959629440 + 15944929280*U + 87653699712*R + 87600697344*R*U + 160425639936*R^2 + 160377864192*R^2*U + 97844723712*R^3 + 97844723712*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 2 := by
    have he : (newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 2 : ℤ) = 1648321920 + 1677721600*U + 5933794176*R + 6039797760*R*U + 5340266496*R^2 + 5435817984*R^2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 (72*R+40) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 2) := by
    have he : (newHeads 8 8 (72*R+40) (4*(1+U)) 2-1-(newEnds 8 8 (72*R+40) (4*(1+U)) (8*(72*R+40)-1) ((1+U)*2) ((1+U)*(4096*R+2222)) true 2) : ℤ) = 31912684160 + 31883284480*U + 175283768448*R + 175177764864*R*U + 320830046208*R^2 + 320734494720*R^2*U + 195689447424*R^3 + 195689447424*R^3*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤(8*(72*R+40)-1)-1 := by
    have he : ((8*(72*R+40)-1)-1 : ℤ) = 318 + 576*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 (72*R+40)-2*(8*(72*R+40)-1) := by
    have he : (T 8 8 (72*R+40)-2*(8*(72*R+40)-1) : ℤ) = 1922 + 3456*R := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*(4096*R+2222)) := by
    have he : (((1+U)*(4096*R+2222)) : ℤ) = 2222 + 2222*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 (72*R+40) (4*(1+U))-2-2*((1+U)*(4096*R+2222)) := by
    have he : (Y 8 8 (72*R+40) (4*(1+U))-2-2*((1+U)*(4096*R+2222)) : ℤ) = 16034 + 16036*U + 28672*R + 28672*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*(4096*R+2222))-((1+U)*2)-1 := by
    have he : (((1+U)*(4096*R+2222))-((1+U)*2)-1 : ℤ) = 2219 + 2220*U + 4096*R + 4096*R*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_0 (U : ℤ) (hU : 0≤U) :
    rowBounds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true ∧ ((1+U)*36)<((1+U)*37) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 0 := by
    have he : (oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 0 : ℤ) = 16636 + 16584*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 2 (4*(1+U)) 0-1-(oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 0) := by
    have he : (oldHeads 8 4 2 (4*(1+U)) 0-1-(oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 0) : ℤ) = 53004 + 53048*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 0 := by
    have he : (newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 0 : ℤ) = 49458 + 49352*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 2 (4*(1+U)) 0-1-(newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 0) := by
    have he : (newHeads 8 4 2 (4*(1+U)) 0-1-(newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 0) : ℤ) = 20182 + 20280*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 1 := by
    have he : (oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 1 : ℤ) = 142698 + 141546*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 2 (4*(1+U)) 1-1-(oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 1) := by
    have he : (oldHeads 8 4 2 (4*(1+U)) 1-1-(oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 1) : ℤ) = 120022 + 120598*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 1 := by
    have he : (newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 1 : ℤ) = 301546 + 299242*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 2 (4*(1+U)) 1-1-(newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 1) := by
    have he : (newHeads 8 4 2 (4*(1+U)) 1-1-(newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 1) : ℤ) = 223894 + 225046*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 2 := by
    have he : (oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 2 : ℤ) = 506976 + 524288*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 2 (4*(1+U)) 2-1-(oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 2) := by
    have he : (oldHeads 8 4 2 (4*(1+U)) 2-1-(oldEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) 2) : ℤ) = 26016 + 8704*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 2 := by
    have he : (newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 2 : ℤ) = 1013984 + 1048576*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 2 (4*(1+U)) 2-1-(newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 2) := by
    have he : (newHeads 8 4 2 (4*(1+U)) 2-1-(newEnds 8 4 2 (4*(1+U)) 3 ((1+U)*36) ((1+U)*37) true 2) : ℤ) = 43296 + 8704*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤3-1 := by
    have he : (3-1 : ℤ) = 2 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 2-2*3 := by
    have he : (T 8 4 2-2*3 : ℤ) = 58 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*37) := by
    have he : (((1+U)*37) : ℤ) = 37 + 37*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 2 (4*(1+U))-2-2*((1+U)*37) := by
    have he : (Y 8 4 2 (4*(1+U))-2-2*((1+U)*37) : ℤ) = 436 + 438*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*37)-((1+U)*36)-1 := by
    have he : (((1+U)*37)-((1+U)*36)-1 : ℤ) = 1*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_1 (U : ℤ) (hU : 0≤U) :
    rowBounds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true ∧ ((1+U)*93)<((1+U)*95) := by
  have h0 : (0:ℤ)≤oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 0 := by
    have he : (oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 0 : ℤ) = 28718 + 28666*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 4 4 (4*(1+U)) 0-1-(oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 0) := by
    have he : (oldHeads 8 4 4 (4*(1+U)) 0-1-(oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 0) : ℤ) = 241626 + 241670*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 0 := by
    have he : (newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 0 : ℤ) = 118884 + 118778*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 4 4 (4*(1+U)) 0-1-(newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 0) := by
    have he : (newHeads 8 4 4 (4*(1+U)) 0-1-(newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 0) : ℤ) = 151460 + 151558*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 1 := by
    have he : (oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 1 : ℤ) = 653694 + 651390*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 4 4 (4*(1+U)) 1-1-(oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 1) := by
    have he : (oldHeads 8 4 4 (4*(1+U)) 1-1-(oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 1) : ℤ) = 396034 + 397186*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 1 := by
    have he : (newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 1 : ℤ) = 1368702 + 1364094*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 4 4 (4*(1+U)) 1-1-(newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 1) := by
    have he : (newHeads 8 4 4 (4*(1+U)) 1-1-(newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 1) : ℤ) = 730754 + 733058*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 2 := by
    have he : (oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 2 : ℤ) = 2025664 + 2097152*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 4 4 (4*(1+U)) 2-1-(oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 2) := by
    have he : (oldHeads 8 4 4 (4*(1+U)) 2-1-(oldEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) 2) : ℤ) = 2202432 + 2130944*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 2 := by
    have he : (newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 2 : ℤ) = 4051392 + 4194304*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 4 4 (4*(1+U)) 2-1-(newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 2) := by
    have he : (newHeads 8 4 4 (4*(1+U)) 2-1-(newEnds 8 4 4 (4*(1+U)) 3 ((1+U)*93) ((1+U)*95) true 2) : ℤ) = 4371008 + 4228096*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤3-1 := by
    have he : (3-1 : ℤ) = 2 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 4 4-2*3 := by
    have he : (T 8 4 4-2*3 : ℤ) = 122 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*95) := by
    have he : (((1+U)*95) : ℤ) = 95 + 95*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 4 4 (4*(1+U))-2-2*((1+U)*95) := by
    have he : (Y 8 4 4 (4*(1+U))-2-2*((1+U)*95) : ℤ) = 832 + 834*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*95)-((1+U)*93)-1 := by
    have he : (((1+U)*95)-((1+U)*93)-1 : ℤ) = 1 + 2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_2 (U : ℤ) (hU : 0≤U) :
    rowBounds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true ∧ ((1+U)*77)<((1+U)*79) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 0 := by
    have he : (oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 0 : ℤ) = 4754 + 4666*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 2 (4*(1+U)) 0-1-(oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 0) := by
    have he : (oldHeads 8 8 2 (4*(1+U)) 0-1-(oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 0) : ℤ) = 134518 + 134598*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 0 := by
    have he : (newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 0 : ℤ) = 41708 + 41530*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 2 (4*(1+U)) 0-1-(newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 0) := by
    have he : (newHeads 8 8 2 (4*(1+U)) 0-1-(newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 0) : ℤ) = 97564 + 97734*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 1 := by
    have he : (oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 1 : ℤ) = 785278 + 782974*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 2 (4*(1+U)) 1-1-(oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 1) := by
    have he : (oldHeads 8 8 2 (4*(1+U)) 1-1-(oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 1) : ℤ) = 264450 + 265602*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 1 := by
    have he : (newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 1 : ℤ) = 1602686 + 1598078*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 2 (4*(1+U)) 1-1-(newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 1) := by
    have he : (newHeads 8 8 2 (4*(1+U)) 1-1-(newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 1) : ℤ) = 496770 + 499074*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 2 := by
    have he : (oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 2 : ℤ) = 2062560 + 2097152*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 2 (4*(1+U)) 2-1-(oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 2) := by
    have he : (oldHeads 8 8 2 (4*(1+U)) 2-1-(oldEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) 2) : ℤ) = 52000 + 17408*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 2 := by
    have he : (newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 2 : ℤ) = 4125152 + 4194304*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 2 (4*(1+U)) 2-1-(newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 2) := by
    have he : (newHeads 8 8 2 (4*(1+U)) 2-1-(newEnds 8 8 2 (4*(1+U)) 5 ((1+U)*77) ((1+U)*79) true 2) : ℤ) = 86560 + 17408*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤5-1 := by
    have he : (5-1 : ℤ) = 4 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 2-2*5 := by
    have he : (T 8 8 2-2*5 : ℤ) = 118 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*79) := by
    have he : (((1+U)*79) : ℤ) = 79 + 79*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 2 (4*(1+U))-2-2*((1+U)*79) := by
    have he : (Y 8 8 2 (4*(1+U))-2-2*((1+U)*79) : ℤ) = 864 + 866*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*79)-((1+U)*77)-1 := by
    have he : (((1+U)*79)-((1+U)*77)-1 : ℤ) = 1 + 2*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_3 (U : ℤ) (hU : 0≤U) :
    rowBounds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true ∧ ((1+U)*192)<((1+U)*193) := by
  have h0 : (0:ℤ)≤oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 0 := by
    have he : (oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 0 : ℤ) = 41432 + 41344*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 8 4 (4*(1+U)) 0-1-(oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 0) := by
    have he : (oldHeads 8 8 4 (4*(1+U)) 0-1-(oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 0) : ℤ) = 499248 + 499328*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 0 := by
    have he : (newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 0 : ℤ) = 205362 + 205184*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 8 4 (4*(1+U)) 0-1-(newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 0) := by
    have he : (newHeads 8 8 4 (4*(1+U)) 0-1-(newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 0) : ℤ) = 335318 + 335488*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 1 := by
    have he : (oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 1 : ℤ) = 3175362 + 3170754*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 8 4 (4*(1+U)) 1-1-(oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 1) := by
    have he : (oldHeads 8 8 4 (4*(1+U)) 1-1-(oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 1) : ℤ) = 1021246 + 1023550*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 1 := by
    have he : (newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 1 : ℤ) = 6473154 + 6463938*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 8 4 (4*(1+U)) 1-1-(newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 1) := by
    have he : (newHeads 8 8 4 (4*(1+U)) 1-1-(newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 1) : ℤ) = 1920062 + 1924670*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 2 := by
    have he : (oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 2 : ℤ) = 8245696 + 8388608*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 8 4 (4*(1+U)) 2-1-(oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 2) := by
    have he : (oldHeads 8 8 4 (4*(1+U)) 2-1-(oldEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) 2) : ℤ) = 8599104 + 8456192*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 2 := by
    have he : (newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 2 : ℤ) = 16491456 + 16777216*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 8 4 (4*(1+U)) 2-1-(newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 2) := by
    have he : (newHeads 8 8 4 (4*(1+U)) 2-1-(newEnds 8 8 4 (4*(1+U)) 5 ((1+U)*192) ((1+U)*193) true 2) : ℤ) = 17130560 + 16844800*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤5-1 := by
    have he : (5-1 : ℤ) = 4 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 8 4-2*5 := by
    have he : (T 8 8 4-2*5 : ℤ) = 246 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*193) := by
    have he : (((1+U)*193) : ℤ) = 193 + 193*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 8 4 (4*(1+U))-2-2*((1+U)*193) := by
    have he : (Y 8 8 4 (4*(1+U))-2-2*((1+U)*193) : ℤ) = 1660 + 1662*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*193)-((1+U)*192)-1 := by
    have he : (((1+U)*193)-((1+U)*192)-1 : ℤ) = 1*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_4 (U : ℤ) (hU : 0≤U) :
    rowBounds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true ∧ ((1+U)*168)<((1+U)*169) := by
  have h0 : (0:ℤ)≤oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 0 := by
    have he : (oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 0 : ℤ) = 1758 + 1616*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 8 16 2 (4*(1+U)) 0-1-(oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 0) := by
    have he : (oldHeads 8 16 2 (4*(1+U)) 0-1-(oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 0) : ℤ) = 276778 + 276912*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 0 := by
    have he : (newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 0 : ℤ) = 67438 + 67152*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 8 16 2 (4*(1+U)) 0-1-(newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 0) := by
    have he : (newHeads 8 16 2 (4*(1+U)) 0-1-(newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 0) : ℤ) = 211098 + 211376*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 1 := by
    have he : (oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 1 : ℤ) = 4012146 + 4007538*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 8 16 2 (4*(1+U)) 1-1-(oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 1) := by
    have he : (oldHeads 8 16 2 (4*(1+U)) 1-1-(oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 1) : ℤ) = 184462 + 186766*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 1 := by
    have he : (newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 1 : ℤ) = 8088178 + 8078962*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 8 16 2 (4*(1+U)) 1-1-(newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 1) := by
    have he : (newHeads 8 16 2 (4*(1+U)) 1-1-(newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 1) : ℤ) = 305038 + 309646*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 2 := by
    have he : (oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 2 : ℤ) = 8319456 + 8388608*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 8 16 2 (4*(1+U)) 2-1-(oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 2) := by
    have he : (oldHeads 8 16 2 (4*(1+U)) 2-1-(oldEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) 2) : ℤ) = 103968 + 34816*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 2 := by
    have he : (newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 2 : ℤ) = 16638944 + 16777216*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 8 16 2 (4*(1+U)) 2-1-(newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 2) := by
    have he : (newHeads 8 16 2 (4*(1+U)) 2-1-(newEnds 8 16 2 (4*(1+U)) 8 ((1+U)*168) ((1+U)*169) true 2) : ℤ) = 173088 + 34816*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤8-1 := by
    have he : (8-1 : ℤ) = 7 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 8 16 2-2*8 := by
    have he : (T 8 16 2-2*8 : ℤ) = 240 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*169) := by
    have he : (((1+U)*169) : ℤ) = 169 + 169*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 8 16 2 (4*(1+U))-2-2*((1+U)*169) := by
    have he : (Y 8 16 2 (4*(1+U))-2-2*((1+U)*169) : ℤ) = 1708 + 1710*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*169)-((1+U)*168)-1 := by
    have he : (((1+U)*169)-((1+U)*168)-1 : ℤ) = 1*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_5 (U : ℤ) (hU : 0≤U) :
    rowBounds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true ∧ ((1+U)*83)<((1+U)*87) := by
  have h0 : (0:ℤ)≤oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 0 := by
    have he : (oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 0 : ℤ) = 247310 + 247142*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 16 8 2 (4*(1+U)) 0-1-(oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 0) := by
    have he : (oldHeads 16 8 2 (4*(1+U)) 0-1-(oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 0) : ℤ) = 834050 + 834202*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 0 := by
    have he : (newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 0 : ℤ) = 624312 + 623974*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 16 8 2 (4*(1+U)) 0-1-(newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 0) := by
    have he : (newHeads 16 8 2 (4*(1+U)) 0-1-(newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 0) : ℤ) = 457048 + 457370*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 1 := by
    have he : (oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 1 : ℤ) = 7333998 + 7325294*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 16 8 2 (4*(1+U)) 1-1-(oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 1) := by
    have he : (oldHeads 16 8 2 (4*(1+U)) 1-1-(oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 1) : ℤ) = 1058962 + 1063314*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 1 := by
    have he : (newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 1 : ℤ) = 14797422 + 14780014*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 16 8 2 (4*(1+U)) 1-1-(newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 1) := by
    have he : (newHeads 16 8 2 (4*(1+U)) 1-1-(newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 1) : ℤ) = 1988498 + 1997202*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 2 := by
    have he : (oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 2 : ℤ) = 16507328 + 16777216*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 16 8 2 (4*(1+U)) 2-1-(oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 2) := by
    have he : (oldHeads 16 8 2 (4*(1+U)) 2-1-(oldEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) 2) : ℤ) = 337472 + 67584*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 2 := by
    have he : (newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 2 : ℤ) = 33014720 + 33554432*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 16 8 2 (4*(1+U)) 2-1-(newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 2) := by
    have he : (newHeads 16 8 2 (4*(1+U)) 2-1-(newEnds 16 8 2 (4*(1+U)) 5 ((1+U)*83) ((1+U)*87) true 2) : ℤ) = 607296 + 67584*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤5-1 := by
    have he : (5-1 : ℤ) = 4 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 16 8 2-2*5 := by
    have he : (T 16 8 2-2*5 : ℤ) = 246 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*87) := by
    have he : (((1+U)*87) : ℤ) = 87 + 87*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 16 8 2 (4*(1+U))-2-2*((1+U)*87) := by
    have he : (Y 16 8 2 (4*(1+U))-2-2*((1+U)*87) : ℤ) = 1872 + 1874*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*87)-((1+U)*83)-1 := by
    have he : (((1+U)*87)-((1+U)*83)-1 : ℤ) = 3 + 4*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_6 (U : ℤ) (hU : 0≤U) :
    rowBounds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true ∧ ((1+U)*204)<((1+U)*205) := by
  have h0 : (0:ℤ)≤oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 0 := by
    have he : (oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 0 : ℤ) = 936000 + 935832*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 16 8 4 (4*(1+U)) 0-1-(oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 0) := by
    have he : (oldHeads 16 8 4 (4*(1+U)) 0-1-(oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 0) : ℤ) = 3323856 + 3324008*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 0 := by
    have he : (newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 0 : ℤ) = 2377962 + 2377624*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 16 8 4 (4*(1+U)) 0-1-(newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 0) := by
    have he : (newHeads 16 8 4 (4*(1+U)) 0-1-(newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 0) : ℤ) = 1881894 + 1882216*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 1 := by
    have he : (oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 1 : ℤ) = 26577946 + 26560538*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 16 8 4 (4*(1+U)) 1-1-(oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 1) := by
    have he : (oldHeads 16 8 4 (4*(1+U)) 1-1-(oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 1) : ℤ) = 6985190 + 6993894*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 1 := by
    have he : (newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 1 : ℤ) = 53661722 + 53626906*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 16 8 4 (4*(1+U)) 1-1-(newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 1) := by
    have he : (newHeads 16 8 4 (4*(1+U)) 1-1-(newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 1) : ℤ) = 13464550 + 13481958*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 2 := by
    have he : (oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 2 : ℤ) = 66012032 + 67108864*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 16 8 4 (4*(1+U)) 2-1-(oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 2) := by
    have he : (oldHeads 16 8 4 (4*(1+U)) 2-1-(oldEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) 2) : ℤ) = 68471936 + 67375104*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 2 := by
    have he : (newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 2 : ℤ) = 132024192 + 134217728*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 16 8 4 (4*(1+U)) 2-1-(newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 2) := by
    have he : (newHeads 16 8 4 (4*(1+U)) 2-1-(newEnds 16 8 4 (4*(1+U)) 5 ((1+U)*204) ((1+U)*205) true 2) : ℤ) = 136677504 + 134483968*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤5-1 := by
    have he : (5-1 : ℤ) = 4 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 16 8 4-2*5 := by
    have he : (T 16 8 4-2*5 : ℤ) = 502 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*205) := by
    have he : (((1+U)*205) : ℤ) = 205 + 205*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 16 8 4 (4*(1+U))-2-2*((1+U)*205) := by
    have he : (Y 16 8 4 (4*(1+U))-2-2*((1+U)*205) : ℤ) = 3684 + 3686*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*205)-((1+U)*204)-1 := by
    have he : (((1+U)*205)-((1+U)*204)-1 : ℤ) = 1*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

private theorem fixed_certificate_7 (U : ℤ) (hU : 0≤U) :
    rowBounds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true ∧ ((1+U)*172)<((1+U)*173) := by
  have h0 : (0:ℤ)≤oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 0 := by
    have he : (oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 0 : ℤ) = 265608 + 265304*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h1 : (0:ℤ)≤oldHeads 16 16 2 (4*(1+U)) 0-1-(oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 0) := by
    have he : (oldHeads 16 16 2 (4*(1+U)) 0-1-(oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 0) : ℤ) = 1897096 + 1897384*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h2 : (0:ℤ)≤newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 0 := by
    have he : (newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 0 : ℤ) = 790202 + 789592*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h3 : (0:ℤ)≤newHeads 16 16 2 (4*(1+U)) 0-1-(newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 0) := by
    have he : (newHeads 16 16 2 (4*(1+U)) 0-1-(newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 0) : ℤ) = 1372502 + 1373096*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h4 : (0:ℤ)≤oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 1 := by
    have he : (oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 1 : ℤ) = 29020314 + 29002906*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h5 : (0:ℤ)≤oldHeads 16 16 2 (4*(1+U)) 1-1-(oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 1) := by
    have he : (oldHeads 16 16 2 (4*(1+U)) 1-1-(oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 1) : ℤ) = 4542822 + 4551526*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h6 : (0:ℤ)≤newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 1 := by
    have he : (newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 1 : ℤ) = 58299546 + 58264730*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h7 : (0:ℤ)≤newHeads 16 16 2 (4*(1+U)) 1-1-(newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 1) := by
    have he : (newHeads 16 16 2 (4*(1+U)) 1-1-(newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 1) : ℤ) = 8826726 + 8844134*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h8 : (0:ℤ)≤oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 2 := by
    have he : (oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 2 : ℤ) = 66569152 + 67108864*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h9 : (0:ℤ)≤oldHeads 16 16 2 (4*(1+U)) 2-1-(oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 2) := by
    have he : (oldHeads 16 16 2 (4*(1+U)) 2-1-(oldEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) 2) : ℤ) = 674880 + 135168*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h10 : (0:ℤ)≤newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 2 := by
    have he : (newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 2 : ℤ) = 133138368 + 134217728*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h11 : (0:ℤ)≤newHeads 16 16 2 (4*(1+U)) 2-1-(newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 2) := by
    have he : (newHeads 16 16 2 (4*(1+U)) 2-1-(newEnds 16 16 2 (4*(1+U)) 9 ((1+U)*172) ((1+U)*173) true 2) : ℤ) = 1214528 + 135168*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h12 : (0:ℤ)≤9-1 := by
    have he : (9-1 : ℤ) = 8 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h13 : (0:ℤ)≤T 16 16 2-2*9 := by
    have he : (T 16 16 2-2*9 : ℤ) = 494 := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h14 : (0:ℤ)≤((1+U)*173) := by
    have he : (((1+U)*173) : ℤ) = 173 + 173*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h15 : (0:ℤ)≤Y 16 16 2 (4*(1+U))-2-2*((1+U)*173) := by
    have he : (Y 16 16 2 (4*(1+U))-2-2*((1+U)*173) : ℤ) = 3748 + 3750*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  have h16 : (0:ℤ)≤((1+U)*173)-((1+U)*172)-1 := by
    have he : (((1+U)*173)-((1+U)*172)-1 : ℤ) = 1*U := by { (try dsimp [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]) <;> ring }; rw [he]; positivity
  refine ⟨⟨?_,by linarith only [h12],by linarith only [h13],h14,by linarith only [h15]⟩,by linarith only [h16]⟩
  intro j
  fin_cases j
  · exact ⟨h0,sub_nonneg.mp h1,h2,sub_nonneg.mp h3⟩
  · exact ⟨h4,sub_nonneg.mp h5,h6,sub_nonneg.mp h7⟩
  · exact ⟨h8,sub_nonneg.mp h9,h10,sub_nonneg.mp h11⟩

theorem residue_bounds (i : Fin 12) (R U : ℤ) (hR : 0≤R) (hU : 0≤U) :
    let f := residueFamilies i
    rowBounds 8 f.p (72*R+f.r) (4*(1+U))
      ((f.p:ℤ)*(72*R+f.r)-1) ((1+U)*f.m0)
      ((1+U)*(512*f.p*R+f.C)) true ∧
      (1+U)*f.m0 < (1+U)*(512*f.p*R+f.C) := by
  fin_cases i
  · exact residue_certificate_0 R U hR hU
  · exact residue_certificate_1 R U hR hU
  · exact residue_certificate_2 R U hR hU
  · exact residue_certificate_3 R U hR hU
  · exact residue_certificate_4 R U hR hU
  · exact residue_certificate_5 R U hR hU
  · exact residue_certificate_6 R U hR hU
  · exact residue_certificate_7 R U hR hU
  · exact residue_certificate_8 R U hR hU
  · exact residue_certificate_9 R U hR hU
  · exact residue_certificate_10 R U hR hU
  · exact residue_certificate_11 R U hR hU

theorem fixed_bounds (i : Fin 8) (U : ℤ) (hU : 0≤U) :
    let f := fixedFamilies i
    rowBounds f.x f.p f.q (4*(1+U)) f.v ((1+U)*f.m0) ((1+U)*f.M0) true ∧
      (1+U)*f.m0 < (1+U)*f.M0 := by
  fin_cases i
  · exact fixed_certificate_0 U hU
  · exact fixed_certificate_1 U hU
  · exact fixed_certificate_2 U hU
  · exact fixed_certificate_3 U hU
  · exact fixed_certificate_4 U hU
  · exact fixed_certificate_5 U hU
  · exact fixed_certificate_6 U hU
  · exact fixed_certificate_7 U hU

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH
