/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoResidualStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoResidualStrip
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: RootTwoResidualStrip at the full original arithmetic domain -/

import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoTailCurve
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Full original residual-strip bound from S.root2curve, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. This is a necessary graph
candidate bound, not a full spectrum criterion, uniform bound in a,
emptiness proof, or a substitute for the open geometric model obligations.
Original Nikandish problem and Ma/Nikandish/Zhang attribution remain. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoResidualStrip
open PairedIdealIntersectionLift RootTwoTailCurve IdealIntersectionObstructions PairedIdealIntersectionObstructions IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph

def candidates (a : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc a (2*a-3)).biUnion (fun b =>
    ((positiveFiber a b)∪positiveThreeFiber a b).image (fun c=>(b,c)))

theorem cardinal_bound (a : ℤ) (ha : 5≤a) :
    (candidates a).card≤4*(a-2).toNat := by
  have hf : ∀ b∈Finset.Icc a (2*a-3),
      (((positiveFiber a b)∪positiveThreeFiber a b).image (fun c=>(b,c))).card≤4 := by
    intro b hb
    calc
      _ ≤ ((positiveFiber a b)∪positiveThreeFiber a b).card:=Finset.card_image_le
      _ ≤ (positiveFiber a b).card+(positiveThreeFiber a b).card:=Finset.card_union_le _ _
      _ ≤4:=by have h2:=fiber_card a b;have h3:=three_fiber_card a b;omega
  have h:=Finset.card_biUnion_le_card_mul (Finset.Icc a (2*a-3))
    (fun b => ((positiveFiber a b)∪positiveThreeFiber a b).image (fun c=>(b,c))) 4 hf
  dsimp only [candidates]
  simpa only [Int.card_Icc,show 2*a-3+1-a=a-2 by ring,Nat.mul_comm] using h

theorem actual_integral_mem (p : Fin 4 → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 5≤a)
    (hb : a≤b) (hb' : b≤2*a-3) (hc : a≤c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    ((b:ℤ),(c:ℤ))∈candidates (a:ℤ) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(b:ℤ),Finset.mem_Icc.mpr ⟨by exact_mod_cast hb,?_⟩,?_⟩
  · have hle : b+3≤2*a:=by omega
    have hleZ : (b:ℤ)+3≤2*(a:ℤ):=by exact_mod_cast hle
    omega
  · apply Finset.mem_image.mpr
    refine ⟨(c:ℤ),?_,rfl⟩
    apply Finset.mem_union.mpr
    rcases PairLowArithmetic.actual_low_root p hp hinj a b c ha hb hc H with h2|h3
    · exact Or.inl ((mem_fiber (a:ℤ) b c (by exact_mod_cast (show 2≤a by omega))
        (by exact_mod_cast (show 0<b by omega)) (by exact_mod_cast (show 0<c by omega))).mpr
        (by rwa [determinant] at h2))
    · exact Or.inr ((mem_three_fiber (a:ℤ) b c (by exact_mod_cast (show 3≤a by omega))
        (by exact_mod_cast (show 0<b by omega)) (by exact_mod_cast (show 0<c by omega))).mpr
        (by rwa [determinant_three] at h3))

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoResidualStrip
