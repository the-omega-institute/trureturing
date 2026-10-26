import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
import Reg.Support.DependentFamily

/-! The original integral and polar coordinate laws with their actual source-form readout. -/

namespace Reg.D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentTopology
open _root_.D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, V n × V n
  State p := V p.1 × V p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p e => sourceTwoForm p.1 p.2 e) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p e => sourceTwoForm p.1 p.2 e + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n q : ℕ,
    signedIncidence n * incidence n = 1 ∧ incidence n * signedIncidence n = 1 ∧
    (∀ (G : Type) [AddCommGroup G] (t : Low n q → G),
      occupationAction n q G t = actionHom n q G t) ∧
    (∀ (G : Type) [AddCommGroup G] (theta eta : Pattern n → G),
      PhaseOrbit n q G theta eta ↔ highPhases (q := q) theta = highPhases (q := q) eta) ∧
    (∀ p0 : PositiveProbability n, (positiveDomain q p0).Nonempty ∧
      IsOpen (positiveDomain q p0) ∧ Convex ℝ (positiveDomain q p0)) ∧
    (∀ (p0 : PositiveProbability n) (x y : positiveDomain q p0 × (High n q → ℝ)),
      quotientCover q p0 x = quotientCover q p0 y ↔ x.1 = y.1 ∧
        ∃ k : High n q → ℤ, ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ)) ∧
    (∀ (x d : V n × V n), (∀ I, 0 < x.1 I) →
      amplitudeOneForm n x d = ∑ T, moments x.1 T * phases d.2 T) ∧
    (∀ d e : V n × V n, R.readout () ⟨n, d⟩ e =
      ∑ T, (phases d.2 T * moments e.1 T - phases e.2 T * moments d.1 T)) ∧
    (∀ (x d e : V n × V n), (∀ I, 0 < x.1 I) → (∑ I, d.1 I = 0) →
      (∑ I, e.1 I = 0) → projectiveTwoForm n x d e = sourceTwoForm n d e) ∧
    (∀ (x : V n × V n), (∀ I, 0 < x.1 I) →
      HasFDerivAt (polarMap n) (polarDerivative n x) x) ∧
    (∀ p theta : V n, polarMap n (p, theta) =
      polarTorusMap n p (fun I => (theta I : Real.Angle))) ∧
    IsLocalHomeomorph (angleCover n q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 0).2.2.2.2.2.2.2.1 0 0
  have hgood := (legal_chain_coordinate_laws 1 0).2.2.2.2.2.2.2.1 0 0
  change sourceTwoForm 1 0 0 + 1 = _ at hbad
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let d : V 1 × V 1 := (0, Pi.single (emptyPattern 1) 1)
  let e : V 1 × V 1 := (Pi.single (emptyPattern 1) 1, 0)
  refine ⟨⟨1, d⟩, 0, e, ?_⟩
  change sourceTwoForm 1 d 0 ≠ sourceTwoForm 1 d e
  simp [sourceTwoForm, d, e, Pi.single_apply, mul_ite]

def registration : Registration arena (∀ n q : ℕ,
    signedIncidence n * incidence n = 1 ∧ incidence n * signedIncidence n = 1 ∧
    (∀ (G : Type) [AddCommGroup G] (t : Low n q → G),
      occupationAction n q G t = actionHom n q G t) ∧
    (∀ (G : Type) [AddCommGroup G] (theta eta : Pattern n → G),
      PhaseOrbit n q G theta eta ↔ highPhases (q := q) theta = highPhases (q := q) eta) ∧
    (∀ p0 : PositiveProbability n, (positiveDomain q p0).Nonempty ∧
      IsOpen (positiveDomain q p0) ∧ Convex ℝ (positiveDomain q p0)) ∧
    (∀ (p0 : PositiveProbability n) (x y : positiveDomain q p0 × (High n q → ℝ)),
      quotientCover q p0 x = quotientCover q p0 y ↔ x.1 = y.1 ∧
        ∃ k : High n q → ℤ, ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ)) ∧
    (∀ (x d : V n × V n), (∀ I, 0 < x.1 I) →
      amplitudeOneForm n x d = ∑ T, moments x.1 T * phases d.2 T) ∧
    (∀ d e : V n × V n, sourceTwoForm n d e =
      ∑ T, (phases d.2 T * moments e.1 T - phases e.2 T * moments d.1 T)) ∧
    (∀ (x d e : V n × V n), (∀ I, 0 < x.1 I) → (∑ I, d.1 I = 0) →
      (∑ I, e.1 I = 0) → projectiveTwoForm n x d e = sourceTwoForm n d e) ∧
    (∀ (x : V n × V n), (∀ I, 0 < x.1 I) →
      HasFDerivAt (polarMap n) (polarDerivative n x) x) ∧
    (∀ p theta : V n, polarMap n (p, theta) =
      polarTorusMap n p (fun I => (theta I : Real.Angle))) ∧
    IsLocalHomeomorph (angleCover n q)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨legal_chain_coordinate_laws, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@legal_chain_coordinate_laws)
    (type_of% (realize.{0, 0, 0, 0, 0} signature
      (fun _ p e => sourceTwoForm p.1 p.2 e) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Fibers.LegalChainMomentCoordinates.legal_chain_coordinate_laws.audit
  realizationName := `Reg.D5.S3.Quantum.Fibers.LegalChainMomentCoordinates.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p e => sourceTwoForm p.1 p.2 e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
