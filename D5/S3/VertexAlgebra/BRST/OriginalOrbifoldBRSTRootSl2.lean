/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRootSl2
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRootSl2
   mirror-E: none(waiver:algebraic-original-orbifold-brst-root-sl2)
   anchors: []
   utility: none
   digest: Each nonzero physical vector of nonisotropic momentum extends to an sl₂ triple. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTOppositeMomentumBracket
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalBPZNondegenerate
import Mathlib.Algebra.Lie.Sl2

/-! Nonisotropic root vectors in the original physical BRST Lie algebra admit
an opposite-momentum partner normalized by the physical BPZ pairing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRootSl2

open LatticeGeneratingFieldLocality (Charge bilinear)
open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData hyperbolic_gram)
open OriginalOrbifoldBRSTCartan (h lie_h_eq_momentum_smul)
open OriginalOrbifoldBRSTMomentum (physicalMomentum physicalMomentum_grading)
open OriginalOrbifoldBRSTOppositeMomentumBracket (H lie_eq_physicalBPZ_smul_H)
open OriginalOrbifoldBRSTPhysicalBPZNondegenerate (physicalBPZ_nondegenerate)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ physicalBPZ_eq_zero_of_momentum)

open private opposite from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

/-- The squared hyperbolic norm in the ordered null coordinates, as a complex scalar. -/
def momentumNormSq (p : UCharge) : ℂ :=
  ∑ i : Fin hyperbolicData.rank, (p i : ℂ) * (p (opposite i) : ℂ)

/-- The scalar used in the root normalization is the native lattice squared norm. -/
theorem momentumNormSq_eq_bilinear (p : UCharge) :
    momentumNormSq p = (bilinear hyperbolicData p p : ℂ) := by
  change (∑ i : Fin 2, (p i : ℂ) * (p (opposite i) : ℂ)) =
    ((∑ i : Fin 2, ∑ j : Fin 2, p i * hyperbolicData.G i j * p j : ℤ) : ℂ)
  rw [hyperbolic_gram]
  simp only [Fin.sum_univ_two, show opposite 0 = 1 from rfl, show opposite 1 = 0 from rfl,
    OrderedHyperbolicExtension.U_zero_zero, OrderedHyperbolicExtension.U_zero_one,
    OrderedHyperbolicExtension.U_one_zero, OrderedHyperbolicExtension.U_one_one,
    mul_zero, zero_mul, mul_one, zero_add, add_zero, Int.cast_add, Int.cast_mul]

set_option maxHeartbeats 1000000 in
-- Sum linearity uses the Lie and module instances on the physical quotient.
/-- The adjoint of the Gram-dual Cartan class on the entire momentum-`q` component. -/
theorem lie_H_eq_momentum_smul (p q : UCharge) (z : DegreeOne)
    (hz : z ∈ physicalMomentum q) :
    ⁅H p, z⁆ = (∑ i : Fin hyperbolicData.rank, (p i : ℂ) * (q (opposite i) : ℂ)) • z := by
  calc
    ⁅H p, z⁆ = ∑ i : Fin hyperbolicData.rank, ⁅(p i : ℂ) • h (opposite i), z⁆ :=
      sum_lie Finset.univ (fun i : Fin hyperbolicData.rank => (p i : ℂ) • h (opposite i)) z
    _ = ∑ i : Fin hyperbolicData.rank, ((p i : ℂ) * (q (opposite i) : ℂ)) • z := by
      refine Finset.sum_congr rfl fun i _ => ?_
      calc
        ⁅(p i : ℂ) • h (opposite i), z⁆ = (p i : ℂ) • ⁅h (opposite i), z⁆ :=
          smul_lie (p i : ℂ) (h (opposite i)) z
        _ = (p i : ℂ) • ((q (opposite i) : ℂ) • z) :=
          congrArg (fun w : DegreeOne => (p i : ℂ) • w)
            (lie_h_eq_momentum_smul (opposite i) q z hz)
        _ = _ := smul_smul (p i : ℂ) (q (opposite i) : ℂ) z
    _ = _ := Finset.sum_smul.symm

set_option maxHeartbeats 1000000 in
-- The kernel and supremum are submodules of the nested physical quotient subtype.
/-- Global nondegeneracy and momentum orthogonality give a partner in the opposite sector. -/
private theorem exists_opposite_physicalBPZ_ne_zero {p : UCharge} {x : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hx0 : x ≠ 0) :
    ∃ y ∈ physicalMomentum (-p), physicalBPZ x y ≠ 0 := by
  classical
  by_contra! hOpposite
  have hker : (⨆ q : UCharge, physicalMomentum q) ≤ LinearMap.ker (physicalBPZ x) := by
    apply iSup_le
    intro q y hy
    apply LinearMap.mem_ker.mpr
    by_cases hq : q = -p
    · subst q
      exact hOpposite y hy
    · exact physicalBPZ_eq_zero_of_momentum hq hx hy
  rw [physicalMomentum_grading.submodule_iSup_eq_top] at hker
  exact hx0 (physicalBPZ_nondegenerate.1 x fun y =>
    LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := y))))

set_option maxHeartbeats 2000000 in
-- The bracket, pairing, and scalar actions are elaborated on the physical quotient subtype.
/-- Every nonzero physical vector of nonisotropic momentum is the positive
generator of an `sl₂` triple for the native physical Lie bracket. -/
theorem exists_root_sl2 {p : UCharge} {x : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hx0 : x ≠ 0) (hp : bilinear hyperbolicData p p ≠ 0) :
    ∃ f ∈ physicalMomentum (-p), IsSl2Triple ((2 / momentumNormSq p) • H p) x f := by
  have hNorm : momentumNormSq p ≠ 0 := by
    rw [momentumNormSq_eq_bilinear]
    exact_mod_cast hp
  have hActionX : ⁅H p, x⁆ = momentumNormSq p • x :=
    lie_H_eq_momentum_smul p p x hx
  have hCartan : H p ≠ 0 := by
    intro hZero
    apply hx0
    apply (Equiv.smulRight (β := DegreeOne) hNorm).injective
    change momentumNormSq p • x = momentumNormSq p • (0 : DegreeOne)
    calc
      momentumNormSq p • x = ⁅H p, x⁆ := hActionX.symm
      _ = ⁅(0 : DegreeOne), x⁆ := congrArg (fun w : DegreeOne => ⁅w, x⁆) hZero
      _ = 0 := zero_lie x
      _ = _ := (smul_zero _).symm
  obtain ⟨y, hy, hPair⟩ := exists_opposite_physicalBPZ_ne_zero hx hx0
  let c : ℂ := 2 / momentumNormSq p
  let f : DegreeOne := (c / physicalBPZ x y) • y
  have hf : f ∈ physicalMomentum (-p) := Submodule.smul_mem _ _ hy
  have hc : c ≠ 0 := div_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hNorm
  have hScaledCartan : c • H p ≠ 0 := by
    intro hZero
    apply hCartan
    apply (Equiv.smulRight (β := DegreeOne) hc).injective
    exact hZero.trans (smul_zero c).symm
  have hNormalize : c * momentumNormSq p = 2 := div_mul_cancel₀ _ hNorm
  have hOppositeWeight :
      (∑ i : Fin hyperbolicData.rank, (p i : ℂ) * ((-p) (opposite i) : ℂ)) =
        -momentumNormSq p := by
    simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, momentumNormSq]
  have hActionF : ⁅H p, f⁆ = -(momentumNormSq p • f) :=
    (lie_H_eq_momentum_smul p (-p) f hf).trans
      ((congrArg (fun a : ℂ => a • f) hOppositeWeight).trans (neg_smul _ f))
  refine ⟨f, hf, ⟨hScaledCartan, ?_, ?_, ?_⟩⟩
  · have hPairF : physicalBPZ x f = c :=
      ((physicalBPZ x).map_smul (c / physicalBPZ x y) y).trans (div_mul_cancel₀ _ hPair)
    exact (lie_eq_physicalBPZ_smul_H hx hf).trans
      (congrArg (fun a : ℂ => a • H p) hPairF)
  · change ⁅c • H p, x⁆ = 2 • x
    calc
      ⁅c • H p, x⁆ = c • ⁅H p, x⁆ := smul_lie c (H p) x
      _ = c • (momentumNormSq p • x) := congrArg (fun w : DegreeOne => c • w) hActionX
      _ = (c * momentumNormSq p) • x := smul_smul c (momentumNormSq p) x
      _ = (2 : ℂ) • x := congrArg (fun a : ℂ => a • x) hNormalize
      _ = 2 • x := (two_smul ℂ x).trans (two_nsmul x).symm
  · change ⁅c • H p, f⁆ = -(2 • f)
    calc
      ⁅c • H p, f⁆ = c • ⁅H p, f⁆ := smul_lie c (H p) f
      _ = c • -(momentumNormSq p • f) := congrArg (fun w : DegreeOne => c • w) hActionF
      _ = -(c • (momentumNormSq p • f)) := smul_neg c (momentumNormSq p • f)
      _ = -((c * momentumNormSq p) • f) :=
        congrArg (fun w : DegreeOne => -w) (smul_smul c (momentumNormSq p) f)
      _ = -((2 : ℂ) • f) := congrArg (fun a : ℂ => -(a • f)) hNormalize
      _ = -(2 • f) := congrArg (fun w : DegreeOne => -w) ((two_smul ℂ f).trans (two_nsmul f).symm)

#print axioms momentumNormSq_eq_bilinear
#print axioms lie_H_eq_momentum_smul
#print axioms exists_opposite_physicalBPZ_ne_zero
#print axioms exists_root_sl2

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRootSl2
