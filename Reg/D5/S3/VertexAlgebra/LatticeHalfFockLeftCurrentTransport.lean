import D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockLeftCurrentTransport UniformGradedLocalCorrelator
open FieldNormalProductLocality
open SupportedFieldWords.OrderedWords SupportedFieldWords.ActualFieldWordAdapter
open CollisionRationalExpansions.OrderedRationalExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev sourceScope := type_of% (@actual_three_field_numerator)

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  b : Carrier D

abbrev signature : Signature where
  Params := Parameters
  State p := ℕ × ℤ × ℤ × ActualTensor p.D p.hu × List (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Distribution 3 (ActualTensor p.D p.hu)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p input =>
    let (K, gamma, delta, x, order) := input
    polynomialAction (weightedClearingPolynomial (threeOrders p.D p.a p.b K))
      (coefficientDistribution (threeFields p.D p.hu p.i p.a p.b gamma delta) x 1 order))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ gamma delta : ℤ,
    (deltaEnd ^ K) (FieldNormalProductLocality.commutator
      (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta)) = 0 ∧
    (∀ d : ℤ, targetSlice p.D p.hu (LatticeFiniteNegativeGeneration.neutralMode p.D p.i d p.a)
      (gamma + 1) = qField 1 d (LatticeSugawaraCurrents.vectorFrequencyBound p.D p.a + 1)
        (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a gamma)) ∧
    (∀ d : ℤ, targetSlice p.D p.hu (LatticeFiniteNegativeGeneration.neutralMode p.D p.i d p.b)
      (delta + 1) = qField 1 d (LatticeSugawaraCurrents.vectorFrequencyBound p.D p.b + 1)
        (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.b delta)) ∧
    (∀ L : ℕ, (deltaEnd ^ L) (FieldNormalProductLocality.commutator
        (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta)) = 0 →
      ∀ s r : ℤ, qField s r K (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta) =
        qField s r L (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta)) ∧
    (∀ r : ℤ,
      FiniteFieldLocality.Local
        (qField gamma r K (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta))
        (targetCurrent p.D p.hu p.i) ∧
      FiniteFieldLocality.Local
        (qField 1 r (LatticeSugawaraCurrents.vectorFrequencyBound p.D p.a + 1)
          (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a gamma)) (targetSlice p.D p.hu p.b delta) ∧
      FiniteFieldLocality.Local
        (qField 1 r (LatticeSugawaraCurrents.vectorFrequencyBound p.D p.b + 1)
          (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.b delta)) (targetSlice p.D p.hu p.a gamma)) ∧
    ∀ x : ActualTensor p.D p.hu,
      (∀ order : List (Fin 3), [0, 1, 2].Perm order →
        R.readout () p (K, gamma, delta, x, order) =
          R.readout () p (K, gamma, delta, x, [0, 1, 2])) ∧
      (∀ label : Fin 3, LowerBoundIn (R.readout () p (K, gamma, delta, x, [0, 1, 2])) label
        (((HahnModule.of ℂ).symm (threeFields p.D p.hu p.i p.a p.b gamma delta label x)).order)) ∧
      (∀ total : ℤ, {e : Exponent 3 | totalExponent e = total ∧
        R.readout () p (K, gamma, delta, x, [0, 1, 2]) e ≠ 0}.Finite) ∧
      (∀ (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ) (sigma : Equiv.Perm (Fin 3)),
        ∃ cleared : HahnSeries (Indices 3) ℂ,
          (∀ e : Exponent 3, cleared.coeff (orderExponents 3 sigma e) =
            phi (R.readout () p (K, gamma, delta, x, [0, 1, 2]) e)) ∧
          scalarWordCarrier 3 (threeFields p.D p.hu p.i p.a p.b gamma delta) sigma x phi =
            (orderedPolynomialFor ℂ 3 sigma
              (weightedClearingPolynomial (threeOrders p.D p.a p.b K)))⁻¹ * cleared)

/-- The family keeps every original parameter and every actual input. -/
theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h p
    exact h p.D p.hu p.i p.a p.b
  · intro h D hu i a b
    exact h ⟨D, hu, i, a, b⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_three_field_numerator)

/- A four-slot registration additionally requires whole-family variation,
sensitivity, observational dependence and enrolled source-selection evidence.
The exact family and source bridge do not assert those obligations. -/

namespace OrderedQ
open scoped VertexOperator

structure Input (p : Parameters) where
  K : ℕ
  gamma : ℤ
  delta : ℤ
  s : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor p.D p.hu
  phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ
  pair : Fin 3

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters Input (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ p input =>
  if input.pair = 0 then
    orderedQReadout input.s input.r input.n input.K
      (targetSlice p.D p.hu p.a input.gamma) (targetSlice p.D p.hu p.b input.delta)
      input.x input.phi
  else if input.pair = 1 then
    orderedQReadout 1 input.r input.n (LatticeSugawaraCurrents.vectorFrequencyBound p.D p.a + 1)
      (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a input.gamma) input.x input.phi
  else
    orderedQReadout 1 input.r input.n (LatticeSugawaraCurrents.vectorFrequencyBound p.D p.b + 1)
      (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.b input.delta) input.x input.phi)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ gamma delta : ℤ,
    (deltaEnd ^ K) (FieldNormalProductLocality.commutator
      (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta)) = 0 ∧
    (∀ (s r n : ℤ) (x : ActualTensor p.D p.hu) (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      phi (((qField s r K (targetSlice p.D p.hu p.a gamma)
        (targetSlice p.D p.hu p.b delta))[[n]]) x) =
      R.readout () p ⟨K, gamma, delta, s, r, n, x, phi, 0⟩) ∧
    (∀ (d n : ℤ) (x : ActualTensor p.D p.hu) (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      phi (((targetSlice p.D p.hu
        (LatticeFiniteNegativeGeneration.neutralMode p.D p.i d p.a) (gamma + 1))[[n]]) x) =
      R.readout () p ⟨K, gamma, delta, 1, d, n, x, phi, 1⟩) ∧
    (∀ (d n : ℤ) (x : ActualTensor p.D p.hu) (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      phi (((targetSlice p.D p.hu
        (LatticeFiniteNegativeGeneration.neutralMode p.D p.i d p.b) (delta + 1))[[n]]) x) =
      R.readout () p ⟨K, gamma, delta, 1, d, n, x, phi, 2⟩)

theorem source_bridge : (type_of% (@actual_ordered_q_coefficients)) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact h p.D p.hu p.i p.a p.b
  · intro h D hu i a b
    exact h ⟨D, hu, i, a, b⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_ordered_q_coefficients)

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let p : Parameters :=
    ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
      Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
      ⟨0, by decide⟩, 0, 0⟩
  obtain ⟨K, h⟩ := law p
  have bad := (h 0 0).2.1 0 0 0 0 0
  have impossible : (0 : ℂ) = 1 := by simpa [rejected, realize] using bad
  exact zero_ne_one impossible

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

/- The actual scalar observations retain all original source and input
parameters. Whole-family rejection can be tested at the zero functional;
observational dependence requires a nonzero actual field coefficient.
An enrolled source-selection binding is also required for Contract.Registration. -/
end OrderedQ

namespace NegativeLaurent
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.RationalFusedResidue

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => ℕ) (fun _ => LaurentSeries ℂ)

def actual : Realization signature := realize signature (fun _ p q =>
  expandX ℂ (localResidue ℂ
    (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)))))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p q : ℕ,
    (∃ first second : List (RatFunc ℂ × ℕ),
      z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)) =
        twoPoleValue true first + twoPoleValue false second) ∧
    R.readout () p q =
      resZ_ZX ℂ (iotaZX ℂ (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)))) -
      resZ_XZ ℂ (iotaXZ ℂ (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ))))

theorem source_bridge : (type_of% (@negative_laurent_collision)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := source_bridge.mp (@negative_laurent_collision)

private theorem right_zero :
    resZ_ZX ℂ (iotaZX ℂ (z ℂ ^ (-(0 : ℤ)) * diagonal ℂ ^ (-(0 : ℤ)))) -
      resZ_XZ ℂ (iotaXZ ℂ (z ℂ ^ (-(0 : ℤ)) * diagonal ℂ ^ (-(0 : ℤ)))) = 0 := by
  simp only [neg_zero, zpow_zero, mul_one, map_one]
  ext n
  by_cases hn : n = 0 <;>
    simp [resZ_ZX, resZ_XZ, HahnSeries.map_coeff, HahnSeries.coeff.linearMap_apply, hn]

private theorem right_one :
    resZ_ZX ℂ (iotaZX ℂ (z ℂ ^ (-(0 : ℤ)) * diagonal ℂ ^ (-(1 : ℤ)))) -
      resZ_XZ ℂ (iotaXZ ℂ (z ℂ ^ (-(0 : ℤ)) * diagonal ℂ ^ (-(1 : ℤ)))) = 1 := by
  simp only [neg_zero, zpow_zero, one_mul, map_zpow₀,
    iotaZX_diagonal, iotaXZ_diagonal, ← kernelZX_zpow, ← kernelXZ_zpow,
    kernelZX_residue, kernelXZ_residue]
  norm_num

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := (law 0 1).2.trans right_one
  exact zero_ne_one impossible

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  have zero := (actual_law 0 0).2.trans right_zero
  have one := (actual_law 0 1).2.trans right_one
  intro bad
  exact zero_ne_one (zero.symm.trans (bad.trans one))

def familyRegistration : Registration arena (type_of% (@negative_laurent_collision)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@negative_laurent_collision) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.negative_laurent_collision
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.NegativeLaurent.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end NegativeLaurent

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
