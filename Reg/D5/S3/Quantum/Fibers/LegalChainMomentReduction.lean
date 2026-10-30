import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.LegalChainMomentReduction
import Reg.Support.DependentFamily

/-! Dependence of the actual source-form pullback on the real tangent directions. -/

namespace Reg.D5.S3.Quantum.Fibers.LegalChainMomentReduction
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentTopology
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentLayers
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentSmooth
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentAtlas
open scoped BigOperators Topology ContDiff Manifold
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, Σ q : ℕ, E n q
  State p := E p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p e =>
    sourceTwoForm p.1 (liftLinear p.1 p.2.1 p.2.2) (liftLinear p.1 p.2.1 e))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p e =>
    sourceTwoForm p.1 (liftLinear p.1 p.2.1 p.2.2) (liftLinear p.1 p.2.1 e) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n q : ℕ) (d e : E n q),
    R.readout () ⟨n, q, d⟩ e = reducedForm n q d e

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 0 0 0
  have hgood := reduced_form_pullback 1 0 0 0
  change sourceTwoForm 1 (liftLinear 1 0 0) (liftLinear 1 0 0) + 1 = _ at hbad
  linarith

private def oneIndex : High 1 0 :=
  ⟨⟨{0}, by simp [Legal]⟩, by simp⟩

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let d : E 1 0 := (0, Pi.single oneIndex 1)
  let e : E 1 0 := (Pi.single oneIndex 1, 0)
  refine ⟨⟨1, 0, d⟩, 0, e, ?_⟩
  change sourceTwoForm 1 (liftLinear 1 0 d) (liftLinear 1 0 0) ≠
    sourceTwoForm 1 (liftLinear 1 0 d) (liftLinear 1 0 e)
  rw [reduced_form_pullback, reduced_form_pullback]
  simp [reducedForm, d, e, Pi.single_apply, mul_ite]

def registration : Registration arena
    (∀ (n q : ℕ) (d e : E n q),
      sourceTwoForm n (liftLinear n q d) (liftLinear n q e) = reducedForm n q d e) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reduced_form_pullback, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reduced_form_pullback)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p e =>
      sourceTwoForm p.1 (liftLinear p.1 p.2.1 p.2.2) (liftLinear p.1 p.2.1 e))
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Fibers.LegalChainMomentReduction.reduced_form_pullback.audit
  realizationName := `Reg.D5.S3.Quantum.Fibers.LegalChainMomentReduction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p e =>
    sourceTwoForm p.1 (liftLinear p.1 p.2.1 p.2.2) (liftLinear p.1 p.2.1 e))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.LegalChainMomentReduction
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The full original coordinate theorem with its actual source pullback observed. -/
abbrev completeArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (hn : 1 ≤ n) (q : ℕ) (p0 : PositiveProbability n),
    ∃ h : Quotient (reductionSetoid q p0) ≃ₜ
        positiveDomain q p0 × (High n q → AddCircle (2 * Real.pi)),
      (∀ a : Representative q p0,
        h (Quotient.mk _ a) = (probabilityFibreEquiv q p0 a.1, highPhases a.2)) ∧
      signedIncidence n * incidence n = 1 ∧ incidence n * signedIncidence n = 1 ∧
      (∀ theta : Pattern n → AddCircle (2 * Real.pi),
        originalPhases (phases theta) = theta ∧ phases (originalPhases theta) = theta) ∧
      (positiveDomain q p0).Nonempty ∧ IsOpen (positiveDomain q p0) ∧
      Convex ℝ (positiveDomain q p0) ∧
      IsManifold (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) ∞ (Quotient (reductionSetoid q p0)) ∧
      (∀ (x y : positiveDomain q p0 × H n q),
        quotientCover q p0 x = quotientCover q p0 y ↔ x.1 = y.1 ∧
          ∃ k : High n q → ℤ, ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ)) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n) (d : V n × V n),
        amplitudeOneForm n (p.val.val, theta) d =
          ∑ T, moments p.val.val T * phases d.2 T) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n) (d e : fixedTangent n q),
        projectiveTwoForm n (p.val.val, theta) d.val e.val =
          reducedForm n q (tangentCoordinates n q d) (tangentCoordinates n q e)) ∧
      (∀ d : fixedTangent n q,
        (∀ e : fixedTangent n q, sourceTwoForm n d.val e.val = 0) ↔
          d ∈ verticalTangent n q) ∧
      (∀ d : E n q, (∀ e, reducedForm n q d e = 0) → d = 0) ∧
      (∀ (x : positiveDomain q p0) (theta : V n),
        ∃ f : H n q × V n → E n q,
          (∀ (y : positiveDomain q p0) (eta : V n),
            chartAt (ModelProd (H n q) (H n q)) (originalPhaseProjection q p0 x theta)
              (originalPhaseProjection q p0 y eta) = f (y.val, eta)) ∧
          HasFDerivAt f
            ((LinearMap.fst ℝ (H n q) (V n)).prod
              ((highPhaseLinear n q).comp (LinearMap.snd ℝ (H n q) (V n)))).toContinuousLinearMap
            (x.val, theta)) ∧
      (∀ (z : E n q), HasFDerivAt (representativeLift q p0)
        (liftLinear n q).toContinuousLinearMap z) ∧
      (∀ (d e : E n q), R.readout () ⟨n, q, d⟩ e =
        reducedForm n q d e) ∧
      (∀ k : ℕ, k ≤ (n + 1) / 2 →
        Fintype.card (Layer n k) = (n - k + 1).choose k) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n),
        ∑ I, Complex.normSq (polarMap n (p.val.val, theta) I) = 1) ∧
      (∀ z : Quotient (reductionSetoid q p0),
        (∀ d : E n q, quotientTwoForm q p0 z d d = 0) ∧
        (∀ d : E n q, (∀ e, quotientTwoForm q p0 z d e = 0) → d = 0) ∧
        (∀ (p : ProbabilityFibre q p0) (theta : V n) (d e : fixedTangent n q),
          quotientTwoForm q p0 z (tangentCoordinates n q d) (tangentCoordinates n q e) =
            projectiveTwoForm n (p.val.val, theta) d.val e.val)) ∧
      (∀ d e : E n q,
        ContMDiff (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) 𝓘(ℝ, ℝ) ∞
          (fun z : Quotient (reductionSetoid q p0) => quotientTwoForm q p0 z d e)) ∧
      (∀ (z : Quotient (reductionSetoid q p0)) (u : positiveDomain q p0 × H n q),
        angleCover n q u.2 ∈ (chartAt (H n q) (reductionHomeomorph q p0 z).2).source →
        HasFDerivAt (liftedChart q p0 z) (ContinuousLinearMap.id ℝ (E n q))
          (u.1.val, u.2)) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n),
        polarMap n (p.val.val, theta) =
          polarTorusMap n p.val.val (fun I => (theta I : Real.Angle)) ∧
        HasFDerivAt (polarMap n) (polarDerivative n (p.val.val, theta))
          (p.val.val, theta)) ∧
      (∀ (u : E n q) (v : Fin 2 → E n q),
        liftedSourceTwoForm q p0 u v = reducedForm n q (v 0) (v 1)) ∧
      (∀ u : E n q, extDeriv (liftedSourceTwoForm q p0) u = 0) ∧
      Fintype.card (Pattern n) = Nat.fib (n + 2) ∧
      (∀ b : Low n q → ℝ, (∀ T, moments p0.val T.val = b T) →
        {p : PositiveProbability n | ∀ T : Low n q, moments p.val T.val = b T} =
          {p : PositiveProbability n | ∀ T : Low n q,
            moments p.val T.val = moments p0.val T.val}) ∧
      (∀ z : Quotient (reductionSetoid q p0),
        Module.finrank ℝ (TangentSpace (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) z) =
          2 * ∑ k ∈ Finset.Ioc q ((n + 1) / 2), (n - k + 1).choose k)

private def uniformOne : PositiveProbability 1 :=
  ⟨fun _ => (Fintype.card (Pattern 1) : ℝ)⁻¹, by
    have hpos : 0 < (Fintype.card (Pattern 1) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨emptyPattern 1⟩
    refine ⟨fun _ => inv_pos.mpr hpos, ?_⟩
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hpos.ne'⟩

private theorem complete_rejected_law : ¬ completeArena.Law rejected := by
  intro h
  obtain ⟨hom, h⟩ := h (n := 1) (by omega) 0 uniformOne
  have hbad := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 0
  have hgood := reduced_form_pullback 1 0 0 0
  change sourceTwoForm 1 (liftLinear 1 0 0) (liftLinear 1 0 0) + 1 = _ at hbad
  linarith

def completeRegistration : Registration completeArena
    (∀ {n : ℕ} (hn : 1 ≤ n) (q : ℕ) (p0 : PositiveProbability n),
    ∃ h : Quotient (reductionSetoid q p0) ≃ₜ
        positiveDomain q p0 × (High n q → AddCircle (2 * Real.pi)),
      (∀ a : Representative q p0,
        h (Quotient.mk _ a) = (probabilityFibreEquiv q p0 a.1, highPhases a.2)) ∧
      signedIncidence n * incidence n = 1 ∧ incidence n * signedIncidence n = 1 ∧
      (∀ theta : Pattern n → AddCircle (2 * Real.pi),
        originalPhases (phases theta) = theta ∧ phases (originalPhases theta) = theta) ∧
      (positiveDomain q p0).Nonempty ∧ IsOpen (positiveDomain q p0) ∧
      Convex ℝ (positiveDomain q p0) ∧
      IsManifold (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) ∞ (Quotient (reductionSetoid q p0)) ∧
      (∀ (x y : positiveDomain q p0 × H n q),
        quotientCover q p0 x = quotientCover q p0 y ↔ x.1 = y.1 ∧
          ∃ k : High n q → ℤ, ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ)) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n) (d : V n × V n),
        amplitudeOneForm n (p.val.val, theta) d =
          ∑ T, moments p.val.val T * phases d.2 T) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n) (d e : fixedTangent n q),
        projectiveTwoForm n (p.val.val, theta) d.val e.val =
          reducedForm n q (tangentCoordinates n q d) (tangentCoordinates n q e)) ∧
      (∀ d : fixedTangent n q,
        (∀ e : fixedTangent n q, sourceTwoForm n d.val e.val = 0) ↔
          d ∈ verticalTangent n q) ∧
      (∀ d : E n q, (∀ e, reducedForm n q d e = 0) → d = 0) ∧
      (∀ (x : positiveDomain q p0) (theta : V n),
        ∃ f : H n q × V n → E n q,
          (∀ (y : positiveDomain q p0) (eta : V n),
            chartAt (ModelProd (H n q) (H n q)) (originalPhaseProjection q p0 x theta)
              (originalPhaseProjection q p0 y eta) = f (y.val, eta)) ∧
          HasFDerivAt f
            ((LinearMap.fst ℝ (H n q) (V n)).prod
              ((highPhaseLinear n q).comp (LinearMap.snd ℝ (H n q) (V n)))).toContinuousLinearMap
            (x.val, theta)) ∧
      (∀ (z : E n q), HasFDerivAt (representativeLift q p0)
        (liftLinear n q).toContinuousLinearMap z) ∧
      (∀ (d e : E n q), sourceTwoForm n (liftLinear n q d) (liftLinear n q e) =
        reducedForm n q d e) ∧
      (∀ k : ℕ, k ≤ (n + 1) / 2 →
        Fintype.card (Layer n k) = (n - k + 1).choose k) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n),
        ∑ I, Complex.normSq (polarMap n (p.val.val, theta) I) = 1) ∧
      (∀ z : Quotient (reductionSetoid q p0),
        (∀ d : E n q, quotientTwoForm q p0 z d d = 0) ∧
        (∀ d : E n q, (∀ e, quotientTwoForm q p0 z d e = 0) → d = 0) ∧
        (∀ (p : ProbabilityFibre q p0) (theta : V n) (d e : fixedTangent n q),
          quotientTwoForm q p0 z (tangentCoordinates n q d) (tangentCoordinates n q e) =
            projectiveTwoForm n (p.val.val, theta) d.val e.val)) ∧
      (∀ d e : E n q,
        ContMDiff (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) 𝓘(ℝ, ℝ) ∞
          (fun z : Quotient (reductionSetoid q p0) => quotientTwoForm q p0 z d e)) ∧
      (∀ (z : Quotient (reductionSetoid q p0)) (u : positiveDomain q p0 × H n q),
        angleCover n q u.2 ∈ (chartAt (H n q) (reductionHomeomorph q p0 z).2).source →
        HasFDerivAt (liftedChart q p0 z) (ContinuousLinearMap.id ℝ (E n q))
          (u.1.val, u.2)) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n),
        polarMap n (p.val.val, theta) =
          polarTorusMap n p.val.val (fun I => (theta I : Real.Angle)) ∧
        HasFDerivAt (polarMap n) (polarDerivative n (p.val.val, theta))
          (p.val.val, theta)) ∧
      (∀ (u : E n q) (v : Fin 2 → E n q),
        liftedSourceTwoForm q p0 u v = reducedForm n q (v 0) (v 1)) ∧
      (∀ u : E n q, extDeriv (liftedSourceTwoForm q p0) u = 0) ∧
      Fintype.card (Pattern n) = Nat.fib (n + 2) ∧
      (∀ b : Low n q → ℝ, (∀ T, moments p0.val T.val = b T) →
        {p : PositiveProbability n | ∀ T : Low n q, moments p.val T.val = b T} =
          {p : PositiveProbability n | ∀ T : Low n q,
            moments p.val T.val = moments p0.val T.val}) ∧
      (∀ z : Quotient (reductionSetoid q p0),
        Module.finrank ℝ (TangentSpace (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) z) =
          2 * ∑ k ∈ Finset.Ioc q ((n + 1) / 2), (n - k + 1).choose k)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_legal_chain_coordinates, rejected, complete_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), complete_rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The full theorem retains its telescope and all unaltered geometric and counting clauses. -/
def completeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_legal_chain_coordinates)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p e =>
      sourceTwoForm p.1 (liftLinear p.1 p.2.1 p.2.2) (liftLinear p.1 p.2.1 e))
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Fibers.LegalChainMomentReduction.complete_legal_chain_coordinates.audit
  realizationName := `Reg.D5.S3.Quantum.Fibers.LegalChainMomentReduction.completeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨completeArena⟩
  objectArena := .source ⟨completeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source completeArena ⟨completeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p e =>
    sourceTwoForm p.1 (liftLinear p.1 p.2.1 p.2.2) (liftLinear p.1 p.2.1 e))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.LegalChainMomentReduction
    definition := none
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Fibers.LegalChainMomentReduction
