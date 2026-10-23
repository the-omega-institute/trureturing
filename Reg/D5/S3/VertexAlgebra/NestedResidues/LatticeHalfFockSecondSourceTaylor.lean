import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact dependent-family reconstruction of the actual J/B rational-field bridge. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
open _root_.D5.S3.VertexAlgebra
open UniformGradedLocalCorrelator LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockChargedTensorCoefficients LatticeGeneratingFieldLocality
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open NestedResidues.LatticeHalfFockSecondSourceTaylor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section

structure Input where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  b : Carrier D
  K : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor D hu
  phi : ActualTensor D hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3
  H : ℕ
  j : ℕ

def signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := SecondSourceField
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => secondSourceTaylorRational s.D s.a s.b s.K s.P s.j)
  (fun empty => nomatch empty)

def coefficientEquation (s : Input) : Prop :=
  ∀ e : Exponent 3, s.P.coeff e =
    if totalExponent e =
        (∑ p ∈ labelledPairs 3, (threeOrders s.D s.a s.b s.K p : ℤ)) - s.d - s.r - s.n - 3
    then s.phi (actualNumerator s.D s.hu s.i s.a s.b s.gamma s.delta s.K s.x e) else 0

def localityEquation (s : Input) : Prop :=
  (FieldNormalProductLocality.deltaEnd ^ s.H)
    (FieldNormalProductLocality.commutator (targetSlice s.D s.hu s.a s.gamma)
      (targetSlice s.D s.hu (neutralMode s.D s.i s.j s.b) (s.delta + 1))) = 0

/-- All original conclusions are retained; the observed rational field varies. -/
def result (s : Input) (G : SecondSourceField) : Prop :=
  let D := s.D
  let hu := s.hu
  let i := s.i
  let a := s.a
  let b := s.b
  let K := s.K
  let gamma := s.gamma
  let delta := s.delta
  let d := s.d
  let r := s.r
  let n := s.n
  let x := s.x
  let phi := s.phi
  let P := s.P
  let H := s.H
  let j := s.j
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let H' := max H (L + M + K)
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    (qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)) =
      qField gamma (d + r - j) H' (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1))) ∧
    (secondSourceRational M j R = G) ∧
    (∀ k l : ℤ,
      lastSourceLocalQ 0 true 1 j M l k R = secondSourceForward G k l ∧
      lastSourceLocalQ 0 false 1 j M k l R = secondSourceBackward G k l) ∧
    QReadoutSupported (d + r - j) H' n
      (secondSourceForward G) (secondSourceBackward G) ∧
    Function.HasFiniteSupport (secondSourceJointTerm false G (d + r - j) n H') ∧
    Function.HasFiniteSupport (secondSourceJointTerm true G (d + r - j) n H') ∧
    Function.HasFiniteSupport
      (secondSourceExpandedJointTerm false D a b K P j (d + r - j) n H') ∧
    Function.HasFiniteSupport
      (secondSourceExpandedJointTerm true D a b K P j (d + r - j) n H') ∧
    (phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      supportedQReadout gamma (d + r - j) H' n
        (secondSourceForward G) (secondSourceBackward G)) ∧
    (phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      secondSourceTaylorOuterReadout D a b K P j gamma (d + r - j) n H') ∧
    OuterQCompletion gamma (d + r - j) n H
      (secondSourceForward G) (secondSourceBackward G)

def arena : Arena where
  signature := signature
  Law R := ∀ s : Input, coefficientEquation s → localityEquation s →
    result s (R.readout () () s)

set_option maxHeartbeats 1000000 in
theorem source_bridge :
    (type_of% (@actual_current_second_source_rational_field)) ↔ arena.Law actual := by
  constructor
  · intro h s coefficients locality
    exact h s.D s.hu s.i s.a s.b s.K s.gamma s.delta s.d s.r s.n s.x s.phi s.P
      coefficients s.H s.j locality
  · intro h D hu i a b K gamma delta d r n x phi P coefficients H j locality
    exact h ⟨D, hu, i, a, b, K, gamma, delta, d, r, n, x, phi, P, H, j⟩ coefficients locality

theorem actual_law : arena.Law actual :=
  source_bridge.mp (@actual_current_second_source_rational_field)

/- Source reconstruction and the positive actual law are supplied.
Whole-family variation, sensitivity, observational dependence and the final
typed registration with its enrolled readout and source binding remain absent.
This partial source makes no declared_validated claim. -/

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
