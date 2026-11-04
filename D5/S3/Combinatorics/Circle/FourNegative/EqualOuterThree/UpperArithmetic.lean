/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/UpperArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-construction-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Consumed upperarithmetic construction for the complete equal-outer-three family. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree

open private Gates
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

private def UpperBounds (q y r z v : ℤ) : Prop :=
  let A := (q+1)*(q*y+1)
  let B := q^2*y+q^2+q+1
  let L := (q+1)*(q^2+1)
  let M := (q^2+q+1)*y+1
  let Bn := 2*B-1
  let Ln := 2*L-q-1
  let Mn := 2*M-1-y-q*y
  Gates (q^3*z-1)
    ((z-v)*L) (M-z*L) ((r-1)*A) (B-r*A)
    ((r-1)*M) (A-r*M) ((r-1)*B+(v-1)*L) (L-r*B) ∧
  Gates (2*q^3*z-1)
    ((z-v)*Ln) (Mn-z*Ln) ((r-1)*(2*A)) (Bn-r*(2*A))
    (A+(r-1)*Mn) (A-r*Mn) ((r-1)*Bn+(v-1)*Ln) (Ln-r*Bn)

set_option maxHeartbeats 1600000 in
private theorem chart_s_ge_three (q m : ℤ) (hq : 4 ≤ q) (hm : 1 ≤ m) :
    UpperBounds (2*q) (8*q*m) q (4*q*m) (3*m) := by
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : ℤ, 0 ≤ Q ∧ q = Q + 4 :=
    ⟨q-4, by omega, by ring⟩
  obtain ⟨H, hH, rfl⟩ : ∃ H : ℤ, 0 ≤ H ∧ m = H + 1 :=
    ⟨m-1, by omega, by ring⟩
  dsimp only [UpperBounds, Gates]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,
    ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | ring

set_option maxHeartbeats 1600000 in
private theorem chart_s_two_large (m : ℤ) (hm : 1 ≤ m) :
    UpperBounds 4 (32*m) 2 (16*m) (5*m) := by
  obtain ⟨H, hH, rfl⟩ : ∃ H : ℤ, 0 ≤ H ∧ m = H + 1 :=
    ⟨m-1, by omega, by ring⟩
  dsimp only [UpperBounds, Gates]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,
    ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | ring

private theorem chart_corner :
    UpperBounds 4 16 2 8 3 := by
  norm_num [UpperBounds, Gates]

end D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
