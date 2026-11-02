/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/LowerArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-construction-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Consumed lowerarithmetic construction for the complete equal-outer-three family. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.LowerArithmetic
open private Gates
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

/- The source has q=2*y*m and y=2*r, with r=2^(b-1) and m=2^(s-b-1).
   Thus r,m>=2.  The polynomial certificate in the caller is the same
   certificate after the harmless even substitution y=2*r; all endpoint
   expressions below are integral and avoid opaque division normalisation. -/
set_option maxHeartbeats 1600000 in
private theorem endpoints (r m : ℤ) (hr : 2 ≤ r) (hm : 2 ≤ m) :
    let y := 2*r
    let q := 2*y*m
    let N := q^3*y-1
    let A := (q+1)*(q*y+1)
    let B := q^2*y+q^2+q+1
    let L := (q+1)*(q^2+1)
    let M := (q^2+q+1)*y+1
    let Bn := 2*B-1
    let Ln := 2*L-q-1
    let Mn := 2*M-1-y-q*y
    let p := m-1
    let H := 64*r^4*m^3
    Gates (H-1) ((2*r*m-1)*M) (A-2*r*m*M)
      ((2*r*m-1)*A) (B-2*r*m*A)
      ((2*r*m-1-p)*B) (L-2*r*m*B)
      ((r-1)*L+p*B) (M-r*L) ∧
    Gates (2*H-1) (A+(2*r*m-1)*Mn) (A-2*r*m*Mn)
      ((2*r*m-1)*(2*A)) (Bn-2*r*m*(2*A))
      ((2*r*m-1-p)*Bn) (Ln-2*r*m*Bn)
      ((r-1)*Ln+p*Bn) (Mn-r*Ln) := by
  obtain ⟨R, hR, rfl⟩ : ∃ R : ℤ, 0 ≤ R ∧ r = R+2 :=
    ⟨r-2, by omega, by ring⟩
  obtain ⟨H0, hH, rfl⟩ : ∃ H0 : ℤ, 0 ≤ H0 ∧ m = H0+2 :=
    ⟨m-2, by omega, by ring⟩
  dsimp only [Gates]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,
    ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  all_goals first
    | (apply sub_nonneg.mp; ring_nf; positivity)
    | (ring_nf; positivity)
    | ring

end D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.LowerArithmetic
