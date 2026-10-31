/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGapsArithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGapsArithmetic
   mirror-E: none(waiver:consumed-endpoint-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Uniform old and enlarged endpoint bounds for a single reserved physical bit. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGapsArithmetic
open private Gates
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

set_option maxHeartbeats 800000 in
private theorem endpoints (p l : ℤ) (hp : 2 ≤ p) (hl : 2 ≤ l) :
    let x := 2*p
    let D := 2*x*l
    let A := x^3+x^2+x+1
    let B := D*(x^2+x+1)+1
    let V := D*(x+1)*x+x+1
    let W := D*x^2+x^2+x+1
    let BV := 2*B-1
    let VW := 2*V-1-x
    let WX := 2*W-1-x-x^2
    let H := x^4*l
    Gates (H-1) ((x*l-1-l)*A) (B-x*l*A) ((p-1)*B) (V-p*B)
      ((p-1)*V) (W-p*V) (l*A+(p-1)*W) (A-p*W) ∧
    Gates (2*H-1) (A+2*(x*l-1-l)*A) (BV-x*l*(2*A))
      ((p-1)*BV) (VW-p*BV) ((p-1)*VW) (WX-p*VW)
      (2*l*A+(p-1)*WX) (A-p*WX) := by
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ p=u+2 := ⟨p-2, by omega, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℤ, 0 ≤ v ∧ l=v+2 := ⟨l-2, by omega, by ring⟩
  dsimp only [Gates]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | ring
end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGapsArithmetic
