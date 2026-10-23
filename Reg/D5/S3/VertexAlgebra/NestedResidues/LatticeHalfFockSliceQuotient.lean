import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact dependent-family source reconstruction for the arbitrary-cutoff quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
open _root_.D5.S3.VertexAlgebra
open UniformGradedLocalCorrelator LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockChargedTensorCoefficients LatticeGeneratingFieldLocality
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open NestedResidues.LatticeHalfFockSliceQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section

/-- The complete original data telescope, including arbitrary actual input and
functional. Coefficient premises remain predicates in the law. -/
structure Input where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  b : Carrier D
  K : ℕ
  K₀ : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor D hu
  phi : ActualTensor D hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3
  P₀ : LabelledPolynomial ℂ 3

def signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CommonRational ℂ 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => algebraMap _ (CommonRational ℂ 3) s.P₀ /
    algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders s.D s.a s.b s.K₀)))
  (fun empty => nomatch empty)

def coefficientEquation (s : Input) (k : ℕ) (Q : LabelledPolynomial ℂ 3) : Prop :=
  ∀ e : Exponent 3, Q.coeff e =
    if totalExponent e =
        (∑ p ∈ labelledPairs 3, (threeOrders s.D s.a s.b k p : ℤ)) - s.d - s.r - s.n - 3
    then s.phi (actualNumerator s.D s.hu s.i s.a s.b s.gamma s.delta k s.x e) else 0

def arena : Arena where
  signature := signature
  Law R := ∀ s : Input, coefficientEquation s s.K s.P → coefficientEquation s s.K₀ s.P₀ →
    let D := s.D
    let hu := s.hu
    let i := s.i
    let a := s.a
    let b := s.b
    let K := s.K
    let K₀ := s.K₀
    let gamma := s.gamma
    let delta := s.delta
    let d := s.d
    let r := s.r
    let n := s.n
    let x := s.x
    let phi := s.phi
    let P := s.P
    let P₀ := s.P₀
    (pairPolynomial (1 : Fin 3) 2 ^ (max K K₀ - K) * P =
      pairPolynomial (1 : Fin 3) 2 ^ (max K K₀ - K₀) * P₀) ∧
    (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3)
          (weightedClearingPolynomial (threeOrders D a b K)) =
      R.readout () () s) ∧
    ∀ (H₁ H₃ : ℕ) (j : ℤ),
      (phi (((qField (gamma + 1) r H₁
          (targetSlice D hu (neutralMode D i d a) (gamma + 1))
          (targetSlice D hu b delta))[[n]]) x) =
        nestedLeftLocalReadout (gamma + 1) 1 d r n (vectorFrequencyBound D a + 1) H₁
          (algebraMap _ (CommonRational ℂ 3) P /
            algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) ∧
       ((FieldNormalProductLocality.deltaEnd ^ H₁)
          (FieldNormalProductLocality.commutator
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta)) = 0 →
        OuterQCompletion (gamma + 1) r n H₁
          (fun k l => currentSourceLocalQ false 1 d (vectorFrequencyBound D a + 1) k l
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))
          (fun k l => currentSourceLocalQ true 1 d (vectorFrequencyBound D a + 1) l k
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))))) ∧
      (phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
        nestedRightLocalReadout 0 gamma 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
          (algebraMap _ (CommonRational ℂ 3) P /
            algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) ∧
       ((FieldNormalProductLocality.deltaEnd ^ H₃)
          (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0 →
        OuterQCompletion gamma (d + r - j) n H₃
          (fun k l => lastSourceLocalQ 0 true 1 j (vectorFrequencyBound D b + 1) l k
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))
          (fun k l => lastSourceLocalQ 0 false 1 j (vectorFrequencyBound D b + 1) k l
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))))


set_option maxHeartbeats 1000000 in
theorem source_bridge :
    (type_of% (@actual_slice_quotient_compat)) ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.D s.hu s.i s.a s.b s.K s.K₀ s.gamma s.delta s.d s.r s.n s.x s.phi s.P s.P₀
  · intro h D hu i a b K K₀ gamma delta d r n x phi P P₀
    exact h ⟨D, hu, i, a, b, K, K₀, gamma, delta, d, r, n, x, phi, P, P₀⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_slice_quotient_compat)

/- The dependent-family proposal preserves the full source reconstruction.
A final Contract.Registration requires whole-family variation, sensitivity,
observational dependence, and exact sourceSelection/escapeFrom evidence.
Those proofs are not supplied here; no declared_validated status is asserted. -/

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
