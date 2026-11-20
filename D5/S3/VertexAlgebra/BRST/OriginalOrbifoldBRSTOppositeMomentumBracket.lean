/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTOppositeMomentumBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTOppositeMomentumBracket
   mirror-E: none(waiver:algebraic-original-orbifold-brst-opposite-momentum)
   anchors: []
   utility: none
   digest: The native opposite-momentum bracket is the BPZ pairing times the dual Cartan vector. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTCartanPairing
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalInvariantBPZ

/-! At opposite momenta the native bracket lies in the Cartan subspace, where
its two BPZ pairings determine it. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTOppositeMomentumBracket

open LatticeGeneratingFieldLocality (Charge)
open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData hyperbolic_gram)
open OriginalOrbifoldBRSTCartan (h h_mem_physicalMomentum_zero lie_h_eq_momentum_smul
  span_h_eq_physicalMomentum_zero)
open OriginalOrbifoldBRSTCartanPairing (physicalBPZ_h physicalBPZ_momentum_zero_nondegenerate)
open OriginalOrbifoldBRSTMomentum (physicalMomentum degreeOne_bracket_mem_physicalMomentum)
open OriginalOrbifoldBRSTPhysicalInvariantBPZ (physicalBPZ_invariant)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ)

open private opposite from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

/-- The Cartan class Gram-dual to the two coordinate values of momentum `p`. -/
def H (p : UCharge) : DegreeOne :=
  ∑ i : Fin hyperbolicData.rank, (p i : ℂ) • h (opposite i)

private theorem H_mem_physicalMomentum_zero (p : UCharge) : H p ∈ physicalMomentum 0 := by
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h_mem_physicalMomentum_zero _)

set_option maxHeartbeats 800000 in
-- Expanding the BPZ pairing of the sum elaborates the physical quotient's linear maps.
private theorem physicalBPZ_H_h (p : UCharge) (i : Fin hyperbolicData.rank) :
    physicalBPZ (H p) (h i) = (p i : ℂ) := by
  simp only [H, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    physicalBPZ_h]
  change (∑ j : Fin 2, (p j : ℂ) * (hyperbolicData.G (opposite j) i : ℂ)) = (p i : ℂ)
  rw [hyperbolic_gram, Fin.sum_univ_two]
  have hop₀ : opposite (0 : Fin hyperbolicData.rank) = 1 := rfl
  have hop₁ : opposite (1 : Fin hyperbolicData.rank) = 0 := rfl
  have hindex : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hindex i with rfl | rfl <;>
    simp only [hop₀, hop₁, OrderedHyperbolicExtension.U_zero_zero,
      OrderedHyperbolicExtension.U_zero_one, OrderedHyperbolicExtension.U_one_zero,
      OrderedHyperbolicExtension.U_one_one, Int.cast_zero, Int.cast_one,
      mul_zero, mul_one, add_zero, zero_add]

set_option maxHeartbeats 2000000 in
-- Passing between the physical quotient and its momentum-zero subtype is costly to elaborate.
/-- The native physical bracket at opposite momenta is the inserted BPZ pairing
times the Cartan vector dual to the momentum of the first input. -/
theorem lie_eq_physicalBPZ_smul_H {p : UCharge} {x y : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hy : y ∈ physicalMomentum (-p)) :
    ⁅x, y⁆ = physicalBPZ x y • H p := by
  have hbracket : ⁅x, y⁆ ∈ physicalMomentum (0 : UCharge) := by
    simpa only [add_neg_cancel] using degreeOne_bracket_mem_physicalMomentum hx hy
  have hpair (i : Fin hyperbolicData.rank) :
      physicalBPZ ⁅x, y⁆ (h i) = (p i : ℂ) * physicalBPZ x y := by
    have hcharge : ((-p) i : ℂ) = -(p i : ℂ) := Int.cast_neg _
    have haction : ⁅y, h i⁆ = (p i : ℂ) • y := calc
      _ = -⁅h i, y⁆ := (lie_skew y (h i)).symm
      _ = -(((-p) i : ℂ) • y) :=
        congrArg (fun z : DegreeOne => -z) (lie_h_eq_momentum_smul i (-p) y hy)
      _ = _ := by rw [hcharge, neg_smul, neg_neg]
    calc
      _ = physicalBPZ x ⁅y, h i⁆ := physicalBPZ_invariant x y (h i)
      _ = physicalBPZ x ((p i : ℂ) • y) := congrArg (fun z => physicalBPZ x z) haction
      _ = _ := (physicalBPZ x).map_smul (p i : ℂ) y
  let difference := ⁅x, y⁆ - physicalBPZ x y • H p
  have hmem : difference ∈ physicalMomentum (0 : UCharge) :=
    Submodule.sub_mem _ hbracket (Submodule.smul_mem _ _ (H_mem_physicalMomentum_zero p))
  have hker : physicalMomentum (0 : UCharge) ≤ LinearMap.ker (physicalBPZ difference) := by
    rw [← span_h_eq_physicalMomentum_zero]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply LinearMap.mem_ker.mpr
    let pairWithCartan : DegreeOne →ₗ[ℂ] ℂ := physicalBPZ.flip (h i)
    change pairWithCartan (⁅x, y⁆ - physicalBPZ x y • H p) = 0
    rw [pairWithCartan.map_sub, pairWithCartan.map_smul]
    change physicalBPZ ⁅x, y⁆ (h i) - physicalBPZ x y * physicalBPZ (H p) (h i) = 0
    calc
      _ = (p i : ℂ) * physicalBPZ x y - physicalBPZ x y * (p i : ℂ) :=
        congrArg₂ (fun a b : ℂ => a - b) (hpair i)
          (congrArg (fun b : ℂ => physicalBPZ x y * b) (physicalBPZ_H_h p i))
      _ = 0 := sub_eq_zero.mpr (mul_comm _ _)
  have hzero : (⟨difference, hmem⟩ : physicalMomentum (0 : UCharge)) = 0 :=
    physicalBPZ_momentum_zero_nondegenerate.1 _ fun z => LinearMap.mem_ker.mp (hker z.property)
  exact sub_eq_zero.mp
    (congrArg (fun z : physicalMomentum (0 : UCharge) => (z : DegreeOne)) hzero)

#print axioms H
#print axioms physicalBPZ_H_h
#print axioms lie_eq_physicalBPZ_smul_H

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTOppositeMomentumBracket
