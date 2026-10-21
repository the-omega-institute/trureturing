import D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
import Reg.Support.SingleDependentReadout

/-! Exact source and scalar observation families for finite actual Laurent windows. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords
open CollisionRationalExpansions.OrderedRationalExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev Parameters := Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.Parameters

structure Input (p : Parameters) where
  K : ℕ
  gamma : ℤ
  delta : ℤ
  x : ActualTensor p.D p.hu
  phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ
  total : ℤ
  P : LabelledPolynomial ℂ 3
  sigma : Equiv.Perm (Fin 3)
  e : Exponent 3

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters Input (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ p input =>
  (orderedRationalFor ℂ 3 input.sigma
    (algebraMap _ (CommonRational ℂ 3) input.P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders p.D p.a p.b input.K)))).coeff
          (orderExponents 3 input.sigma input.e)) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ (gamma delta : ℤ) (x : ActualTensor p.D p.hu)
      (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ) (total : ℤ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e = if totalExponent e = total then
          phi (actualNumerator p.D p.hu p.i p.a p.b gamma delta K x e) else 0) ∧
        ∀ (sigma : Equiv.Perm (Fin 3)) (e : Exponent 3),
          R.readout () p ⟨K, gamma, delta, x, phi, total, P, sigma, e⟩ =
            if totalExponent e = total - ∑ q ∈ labelledPairs 3,
              (threeOrders p.D p.a p.b K q : ℤ)
            then phi (coefficientDistribution (threeFields p.D p.hu p.i p.a p.b gamma delta)
              x 1 (List.ofFn sigma) e) else 0

theorem source_bridge : (type_of% (@actual_finite_laurent_carriers)) ↔ arena.Law actual := by
  constructor
  · intro h p
    obtain ⟨K, hp⟩ := h p.D p.hu p.i p.a p.b
    refine ⟨K, ?_⟩
    intro gamma delta x phi total
    obtain ⟨P, coefficients, observations⟩ := hp gamma delta x phi total
    refine ⟨P, coefficients, ?_⟩
    intro sigma e
    simpa [actual, realize] using observations sigma e
  · intro h D hu i a b
    obtain ⟨K, hp⟩ := h ⟨D, hu, i, a, b⟩
    refine ⟨K, ?_⟩
    intro gamma delta x phi total
    obtain ⟨P, coefficients, observations⟩ := hp gamma delta x phi total
    refine ⟨P, coefficients, ?_⟩
    intro sigma e
    simpa [actual, realize] using observations sigma e

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_finite_laurent_carriers)

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let p : Parameters :=
    ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
      Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
      ⟨0, by decide⟩, 0, 0⟩
  obtain ⟨K, h⟩ := law p
  let d : ℤ := ∑ q ∈ labelledPairs 3, (threeOrders p.D p.a p.b K q : ℤ)
  obtain ⟨P, _, observations⟩ := h 0 0 0 0 (d + 1)
  have bad := observations (Equiv.refl _) 0
  have impossible : (1 : ℂ) = 0 := by
    simpa [rejected, realize] using bad
  exact one_ne_zero impossible

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

theorem laurent_dependence : ObservationalDependence signature actual := by
  intro role
  let p : Parameters :=
    ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
      Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
      ⟨0, by decide⟩, 0, 0⟩
  let Q := weightedClearingPolynomial (threeOrders p.D p.a p.b 0)
  have Qnonzero : Q ≠ 0 := by
    have uniformNonzero : UniformGradedLocalCorrelator.clearingPolynomial 3 1 ≠ 0 :=
      SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 3 0 1
    have pairs : ∀ q ∈ labelledPairs 3, pairPolynomial q.1 q.2 ≠ 0 := by
      simpa only [UniformGradedLocalCorrelator.clearingPolynomial, pow_one] using
        Finset.prod_ne_zero_iff.mp uniformNonzero
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => pow_ne_zero _ (pairs q hq))
  have denominator : algebraMap _ (CommonRational ℂ 3) Q ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (LabelledPolynomial ℂ 3) (CommonRational ℂ 3)).ne Qnonzero
  let input (P : LabelledPolynomial ℂ 3) : Input p := ⟨0, 0, 0, 0, 0, 0, P, Equiv.refl _, 0⟩
  refine ⟨p, input 0, input Q, ?_⟩
  change (orderedRationalFor ℂ 3 (Equiv.refl _)
      (algebraMap _ (CommonRational ℂ 3) 0 / algebraMap _ (CommonRational ℂ 3) Q)).coeff
        (orderExponents 3 (Equiv.refl _) 0) ≠
    (orderedRationalFor ℂ 3 (Equiv.refl _)
      (algebraMap _ (CommonRational ℂ 3) Q / algebraMap _ (CommonRational ℂ 3) Q)).coeff
        (orderExponents 3 (Equiv.refl _) 0)
  rw [map_zero, zero_div, map_zero, div_self denominator, map_one, map_zero]
  simp

def finiteFamilyRegistration : Registration arena (type_of% (@actual_finite_laurent_carriers)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := laurent_dependence

def finiteRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_finite_laurent_carriers) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout.actual_finite_laurent_carriers
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout.finiteFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨finiteFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

namespace BinaryTaylor
open scoped VertexOperator

structure Input (p : Parameters) where
  K : ℕ
  gamma : ℤ
  delta : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor p.D p.hu
  phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 2
  s : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters Input (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ p input =>
  Finsupp.linearCombination ℂ (fun e : Exponent 2 =>
    if totalExponent e = (input.K : ℤ) - input.r - input.n - 2 then
      Ring.choose ((e 0 : ℂ) - (input.s : ℂ) / 2)
        ((input.K : ℤ) - input.r - 1).toNat else 0) input.P.coeff)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ (gamma delta r n : ℤ), r < K →
      ∀ (x : ActualTensor p.D p.hu) (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 2,
        (∀ e, P.coeff e = if totalExponent e = (K : ℤ) - r - n - 2 then
          phi (binaryNumerator (targetSlice p.D p.hu p.a gamma)
            (targetSlice p.D p.hu p.b delta) K x e) else 0) ∧
        ∀ s : ℤ, phi (((qField s r K (targetSlice p.D p.hu p.a gamma)
            (targetSlice p.D p.hu p.b delta))[[n]]) x) =
          R.readout () p ⟨K, gamma, delta, r, n, x, phi, P, s⟩

theorem source_bridge : (type_of% (@actual_binary_taylor_readout)) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact h p.D p.hu p.i p.a p.b
  · intro h D hu i a b
    obtain ⟨K, hp⟩ := h ⟨D, hu, i, a, b⟩
    refine ⟨K, ?_⟩
    intro gamma delta r n below x phi
    obtain ⟨P, coefficients, observation⟩ := hp gamma delta r n below x phi
    refine ⟨P, coefficients, ?_⟩
    intro s
    simpa [actual, realize] using observation s

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_binary_taylor_readout)

private def witness : Parameters :=
  ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
    Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
    ⟨0, by decide⟩, 0, 0⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨K, h⟩ := law witness
  obtain ⟨P, _, observations⟩ := h 0 0 (K - 1) 0 (by omega) 0 0
  have bad := observations 0
  have impossible : (0 : ℂ) = 1 := by simpa [rejected, realize] using bad
  exact zero_ne_one impossible

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let input (P : LabelledPolynomial ℂ 2) : Input witness := ⟨0, 0, 0, -1, -1, 0, 0, P, 0⟩
  refine ⟨witness, input 0, input (AddMonoidAlgebra.single 0 1), ?_⟩
  norm_num [actual, realize, input, AddMonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single, totalExponent]

def familyRegistration : Registration arena (type_of% (@actual_binary_taylor_readout)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_binary_taylor_readout) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout.actual_binary_taylor_readout
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout.BinaryTaylor.familyRegistration
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end BinaryTaylor

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
