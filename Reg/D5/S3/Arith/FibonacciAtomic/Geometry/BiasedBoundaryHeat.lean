import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Full original-carrier heat statement with an extended-trace observation.
The typed family evidence does not assert raw source-selection validation. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat
open BiasedBoundaryTrace (G)
open BiasedBoundaryStopping (G0)
open BiasedBoundaryFreeRootForm (K Sigma)
open BiasedBoundaryCentering (C)
open BiasedBoundaryOperator (boundaryOperator)
open MarkovProcess.Semigroup Filter
open _root_.D5.S3.HilbertOperators.RealPositiveTrace (positiveTrace)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Topology ENNReal InnerProductSpace

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs :=
    ∃ (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
      (hp : ∀ i, 0 < mu i),
      Antitone mu ∧ Tendsto mu atTop (𝓝 0) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) ∧
      G0.subtypeL.comp BiasedBoundaryOperator.centeredTrace = C ∧
      BiasedBoundaryOperator.centeredTrace.adjoint.comp BiasedBoundaryOperator.centeredTrace = BiasedBoundaryFreeRootForm.Sigma ∧
      (∀ i, BiasedBoundaryOperator.centeredTrace (k i).val = Real.sqrt (mu i) • e i) ∧
      Tendsto (fun lam : ℝ => Real.log (BiasedBoundaryCounting.positiveCount mu lam : ℝ) /
        Real.log lam) atTop (𝓝 1) ∧
      Tendsto (fun j : ℕ => Real.log (BiasedBoundaryCounting.positiveEigenvalue mu j) /
        Real.log (j : ℝ)) atTop (𝓝 1) ∧
      ∃ S : StronglyContinuousContractionSemigroup G0,
        (∀ t, S t = heat e mu hp t) ∧
        (∀ t, (S t).IsPositive ∧ obs.readout () () (positiveTrace (S t)) =
          ∑' i, ENNReal.ofReal (Real.exp (-(t : ℝ) * (mu i)⁻¹))) ∧
        (∀ t : ℝ≥0, 0 < t →
          Summable (fun i => Real.exp (-(t : ℝ)*(mu i)⁻¹)) ∧
          obs.readout () () (positiveTrace (S t)) < ⊤ ∧
          (BiasedBoundaryTrace.b/(t : ℝ))*Real.exp (-(t : ℝ)/BiasedBoundaryTrace.b) ≤
            (obs.readout () () (positiveTrace (S t))).toReal ∧
          (obs.readout () () (positiveTrace (S t))).toReal ≤ BiasedBoundaryCounting.B/(t : ℝ) ∧
          ((t : ℝ) ≤ BiasedBoundaryTrace.b →
            BiasedBoundaryTrace.b/(Real.exp 1*(t : ℝ)) ≤ (obs.readout () () (positiveTrace (S t))).toReal)) ∧
        (∀ t : ℝ≥0, 0 < t →
          MeasureTheory.IntegrableOn
            (fun u : ℝ => Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ))
            (Set.Ioi 0) ∧
          (obs.readout () () (positiveTrace (S t))).toReal = (t : ℝ)*∫ u : ℝ in Set.Ioi 0,
            Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ)) ∧
        (∀ u v : G0, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t u-u))
          (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph) ∧
        (∀ R : StronglyContinuousContractionSemigroup G0,
          (∀ u v : G0, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t u-u))
            (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph) → R = S) ∧
        ∃ T : StronglyContinuousContractionSemigroup G,
          (∀ t, T t = fullHeat e mu hp t) ∧
          (∀ t, (T t).IsPositive ∧ obs.readout () () (positiveTrace (T t)) = 1+obs.readout () () (positiveTrace (S t))) ∧
          (∀ t : ℝ≥0, 0 < t → obs.readout () () (positiveTrace (T t)) < ⊤ ∧
            (obs.readout () () (positiveTrace (T t))).toReal = 1+(obs.readout () () (positiveTrace (S t))).toReal) ∧
          Tendsto (fun t : ℝ≥0 => Real.log (obs.readout () () (positiveTrace (S t))).toReal /
            Real.log (1/(t : ℝ))) (𝓝[>] 0) (𝓝 1) ∧
          Tendsto (fun t : ℝ≥0 => Real.log (obs.readout () () (positiveTrace (T t))).toReal /
            Real.log (1/(t : ℝ))) (𝓝[>] 0) (𝓝 1) ∧
          (∀ t c, T t (BiasedBoundaryPathSplit.constG c) = BiasedBoundaryPathSplit.constG c) ∧
          (∀ t (x : G0), T t x.val = (S t x).val) ∧
          (∀ F V : G, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t F-F))
            (𝓝[>] 0) (𝓝 V) ↔ (F,-V) ∈ boundaryOperator.graph) ∧
          (∀ R : StronglyContinuousContractionSemigroup G,
            (∀ F V : G, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t F-F))
              (𝓝[>] 0) (𝓝 V) ↔ (F,-V) ∈ boundaryOperator.graph) → R = T)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨e,k,mu,hp,hm,ht,hk,hC,hinclusion,hgram,hcentered,hcount,heigen,S,hS,htr,hfin,hlaplace,hgen,huniq,hfull⟩
  have ht := (hfin 1 (by norm_num)).2.1
  exact (lt_irrefl (⊤ : ℝ≥0∞)) ht

def familyRegistration : Registration arena (type_of% actual_heat) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_heat,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(),0,1,zero_ne_one⟩

/-- Typed attempt; the raw occurrence selection remains an unvalidated gap. -/
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_heat)
    (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat
