/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRelativeDescentAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRelativeDescentAdjoint
   mirror-E: none(waiver:algebraic-original-brst-relative-descent-adjoint)
   anchors: []
   utility: none
   digest: The corrected ambient descent adjunction transfers to the inserted relative BPZ form. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescentAdjointHomotopy
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZNondegenerate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalPairing
import Batteries.Tactic.OpenPrivate

/-! The ambient antighost transpose and nondegeneracy control the commutator
with the ghost insertion. The relative Ward identity kills the remaining
positive-mode corrections through their BRST primitive. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRelativeDescentAdjoint

open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTStateField (Y)
open OriginalOrbifoldBRSTFieldAxioms (stateField_parity)
open OriginalOrbifoldBRSTDescent (descent descent_b_zero cycleDescent relativeStates
  relativeCycles relativeDifferential relativeDifferential_square relativeBoundaries
  RelativeCohomology cohomologyDescent_mk)
open OriginalOrbifoldBRSTDescentAdjointHomotopy
  (descentAdjointCorrection descentAdjointHomotopy descentAdjointCorrection_exact)
open OriginalOrbifoldBRSTBPZWard (betaTotal betaRelTotal)
open OriginalOrbifoldBRSTBPZNondegenerate (betaTotal_nondegenerate)
open OriginalOrbifoldBRSTPhysicalPairing
  (betaRelTotal_right_boundary physicalBPZ physicalBPZ_representatives)
open OriginalOrbifoldBRSTPhysicalLie (N DegreeOne homogeneous_cycle_lift degreeOne_bracket)

open private b_parity parity_square cycle_closed from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private c0 b_zero_c_zero_car b_zero_of_relative betaTotal_b_zero betaTotal_isotropic from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
open private number_one_parity from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

/-- The ambient adjunction including the first `n` positive-order corrections
at every cutoff where the next iterate of the descent field state vanishes. -/
def AmbientDescentAdjunction (u : State) : Prop :=
  ∀ (n : ℕ), ((VirasoroBRST.Ltotal matterDatum 1) ^ (n + 1)) (b (-1) u) = 0 →
    ∀ x y : State, betaTotal (descent u x) y =
      -betaTotal x (descent u y + descentAdjointCorrection n u y)

/-- The corrected ambient adjunction makes descent by an odd cycle skew-adjoint
for the inserted BPZ form on relative cycles. -/
theorem betaRelTotal_cycleDescent_skew_adjoint (u v w : relativeCycles)
    (hp : parity (u.1 : State) = -(u.1 : State))
    (hadj : AmbientDescentAdjunction (u.1 : State)) :
    betaRelTotal (cycleDescent u v : relativeStates) (w : relativeStates) =
      -betaRelTotal (v : relativeStates) (cycleDescent u w : relativeStates) := by
  obtain ⟨n, hn, _, _, hrelative, hexact⟩ :=
    descentAdjointCorrection_exact (u.1 : State) (w.1 : State) u.1.property
      (cycle_closed u) hp w.1.property (cycle_closed w)
  let A := descent (u.1 : State)
  let Aop (y : State) : State := -(A y + descentAdjointCorrection (n + 1) (u.1 : State) y)
  have htranspose (x y : State) : betaTotal (A x) y = betaTotal x (Aop y) := by
    simpa only [A, Aop, map_neg] using hadj (n + 1) hn x y
  have hu := b_zero_of_relative (u : relativeStates)
  have hA_b (x : State) : b 0 (A x) = A (b 0 x) := by
    simpa only [A, hu, hp, map_zero, LinearMap.zero_apply, map_neg, LinearMap.neg_apply,
      neg_zero, zero_sub, neg_neg] using descent_b_zero (u.1 : State) x
  have heven : parity (b (-1) (u.1 : State)) = b (-1) (u.1 : State) := by
    rw [b_parity, hp, map_neg, neg_neg]
  have hA_parity (x : State) : parity (A x) = A (parity x) := by
    change parity (((Y (b (-1) (u.1 : State)))[[0]]) x) =
      ((Y (b (-1) (u.1 : State)))[[0]]) (parity x)
    have h := LinearMap.congr_fun (stateField_parity (b (-1) (u.1 : State)) 0) x
    simpa only [Module.End.mul_apply, heven] using h
  have hAop_b (y : State) : b 0 (Aop y) = Aop (b 0 y) := by
    apply sub_eq_zero.mp
    refine betaTotal_nondegenerate.2 _ (fun x => ?_)
    rw [(betaTotal x).map_sub]
    apply sub_eq_zero.mpr
    calc
      betaTotal x (b 0 (Aop y)) = betaTotal (b 0 (parity x)) (Aop y) := by
        rw [betaTotal_b_zero, parity_square]
      _ = betaTotal (A (b 0 (parity x))) y := (htranspose _ _).symm
      _ = betaTotal (b 0 (parity (A x))) y := by rw [hA_parity, hA_b]
      _ = betaTotal (A x) (b 0 y) := by rw [betaTotal_b_zero, parity_square]
      _ = betaTotal x (Aop (b 0 y)) := htranspose _ _
  have hcar (z : State) (hz : b 0 z = 0) : b 0 (c0 z) = z := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hz, map_zero, add_zero,
      Module.End.one_apply] using LinearMap.congr_fun b_zero_c_zero_car z
  have hw := b_zero_of_relative (w : relativeStates)
  have hAop_w : b 0 (Aop (w.1 : State)) = 0 := by
    rw [hAop_b, hw]
    refine betaTotal_nondegenerate.2 _ (fun x => ?_)
    rw [← htranspose x 0, (betaTotal (A x)).map_zero]
  have hdiff : b 0 (Aop (c0 (w.1 : State)) - c0 (Aop (w.1 : State))) = 0 := by
    rw [map_sub, hAop_b, hcar _ hw, hcar _ hAop_w, sub_self]
  have hinsert : betaTotal (v.1 : State) (Aop (c0 (w.1 : State))) =
      betaTotal (v.1 : State) (c0 (Aop (w.1 : State))) := by
    apply sub_eq_zero.mp
    rw [← (betaTotal (v.1 : State)).map_sub]
    exact betaTotal_isotropic (b_zero_of_relative (v : relativeStates)) hdiff
  let primitive : relativeStates :=
    ⟨descentAdjointHomotopy (n + 1) (u.1 : State) (w.1 : State), hrelative⟩
  let boundary := boundaryMap relativeDifferential relativeDifferential_square primitive
  have hboundary : boundary ∈ relativeBoundaries := ⟨primitive, rfl⟩
  have hcorrection :
      betaTotal (v.1 : State) (c0 (descentAdjointCorrection (n + 1) (u.1 : State) (w.1 : State))) =
        0 := by
    rw [← hexact]
    exact betaRelTotal_right_boundary v boundary hboundary
  change betaTotal (A (v.1 : State)) (c0 (w.1 : State)) =
    -betaTotal (v.1 : State) (c0 (A (w.1 : State)))
  calc
    _ = betaTotal (v.1 : State) (Aop (c0 (w.1 : State))) := htranspose _ _
    _ = betaTotal (v.1 : State) (c0 (Aop (w.1 : State))) := hinsert
    _ = _ := by simp only [Aop, map_neg, map_add, hcorrection, add_zero]

-- Elaborating homogeneous representatives compares the native cycle and quotient types.
set_option maxHeartbeats 2000000 in
/-- Ambient adjunction on degree-one cycle representatives makes their induced
physical Lie action skew-adjoint for the physical BPZ form. -/
theorem physicalBPZ_bracket_skew_adjoint
    (hadj : ∀ u : relativeCycles, N (u.1 : State) = (u.1 : State) →
      AmbientDescentAdjunction (u.1 : State))
    (a b c : DegreeOne) :
    physicalBPZ ⁅a, b⁆ c = -physicalBPZ b ⁅a, c⁆ := by
  have lift (d : DegreeOne) : ∃ z : relativeCycles,
      relativeBoundaries.mkQ z = (d : RelativeCohomology) ∧
        N (z.1 : State) = (z.1 : State) := by
    simpa only [Int.cast_one, one_smul] using
      homogeneous_cycle_lift 1 (d : RelativeCohomology) d.property
  let u : relativeCycles := (lift a).choose
  let v : relativeCycles := (lift b).choose
  let w : relativeCycles := (lift c).choose
  have hu : relativeBoundaries.mkQ u = (a : RelativeCohomology) := (lift a).choose_spec.1
  have hv : relativeBoundaries.mkQ v = (b : RelativeCohomology) := (lift b).choose_spec.1
  have hw : relativeBoundaries.mkQ w = (c : RelativeCohomology) := (lift c).choose_spec.1
  have hNu : N (u.1 : State) = (u.1 : State) := (lift a).choose_spec.2
  have bracket_mk (x y : relativeCycles) (p q : DegreeOne)
      (hx : relativeBoundaries.mkQ x = (p : RelativeCohomology))
      (hy : relativeBoundaries.mkQ y = (q : RelativeCohomology)) :
      relativeBoundaries.mkQ (cycleDescent x y) = (↑⁅p, q⁆ : RelativeCohomology) := by
    rw [degreeOne_bracket, ← hx, ← hy, cohomologyDescent_mk]
  calc
    physicalBPZ ⁅a, b⁆ c =
        betaRelTotal (cycleDescent u v : relativeStates) (w : relativeStates) :=
      physicalBPZ_representatives _ _ (cycleDescent u v) w (bracket_mk u v a b hu hv) hw
    _ = -betaRelTotal (v : relativeStates) (cycleDescent u w : relativeStates) :=
      betaRelTotal_cycleDescent_skew_adjoint u v w (number_one_parity (u.1 : State) hNu)
        (hadj u hNu)
    _ = -physicalBPZ b ⁅a, c⁆ := by
      rw [physicalBPZ_representatives _ _ v (cycleDescent u w) hv (bracket_mk u w a c hu hw)]

#print axioms AmbientDescentAdjunction
#print axioms betaRelTotal_cycleDescent_skew_adjoint
#print axioms physicalBPZ_bracket_skew_adjoint

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRelativeDescentAdjoint
