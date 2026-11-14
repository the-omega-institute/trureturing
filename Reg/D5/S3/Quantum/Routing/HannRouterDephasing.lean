import D5.S3.Quantum.Routing.HannRouterDephasing
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The complete physical-router source telescope, with fidelity as dependent readout. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Reg.D5.S3.Quantum.Routing.HannRouterDephasing

open _root_.D5.S3.Quantum.Routing.HannRouterDephasing
open _root_.D5.S3.Quantum.Routing.HannSpatialQram
open _root_.D5.S3.Quantum.Routing.ReversibleQram (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, ℝ × (Address n → Bool))
    (fun p => Address p.1 × Bool → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p ψ => squaredFidelity p.1 p.2.1 p.2.2 ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceLaw (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) (D : Address n → Bool),
    (∀ (X : Matrix Qutrit Qutrit ℂ) (s t : Qutrit),
      (∑ e, localRecord q s e * conj (localRecord q t e)) * X s t =
        (q : ℂ) * X s t + (1-(q : ℂ)) * (if s = t then X s t else 0)) ∧
    (∀ t : _root_.D5.S3.Quantum.Routing.HannSpatialQram.Tree n, recordOverlap n q t t = 1) ∧
    (∀ (a a' : Address n) (b b' : Bool),
      routerMismatch n ((load n n) (clean n a b)).2.2
        ((load n n) (clean n a' b')).2.2 =
          (if a = a' then 0 else 2 * (n -
            (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
              (addressWord n a) (addressWord n a')).length) - 1) ∧
      recordOverlap n q ((load n n) (clean n a b)).2.2
        ((load n n) (clean n a' b')).2.2 = (kernel n q a a' : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s t : State n),
      (∑ e, jointOutput n q D ψ s e * conj (jointOutput n q D ψ t e)) =
        noisyOutput n q D ψ s t) ∧
    (∀ (ψ : Address n × Bool → ℂ) (a a' : Address n) (b b' : Bool),
      noisyOutput n q D ψ (clean n a (xor b (D a))) (clean n a' (xor b' (D a'))) =
        ψ (a,b) * conj (ψ (a',b')) * (kernel n q a a' : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s t : State n),
      ((∀ a b, s ≠ clean n a b) ∨ (∀ a b, t ≠ clean n a b)) →
        noisyOutput n q D ψ s t = 0) ∧
    (∀ ψ : Address n × Bool → ℂ, Normalized n ψ →
      (∑ s, Complex.normSq (idealOutput n D ψ s)) = 1 ∧
      R.readout () ⟨n,q,D⟩ ψ = (addressEnergy n q (addressProbability n ψ) : ℂ) ∧
        minimumFidelity n q ≤ (R.readout () ⟨n,q,D⟩ ψ).re) ∧
    Normalized n (uniformInput n) ∧
      R.readout () ⟨n,q,D⟩ (uniformInput n) = (minimumFidelity n q : ℂ) ∧
      minimumFidelity 0 q = 1 ∧
      (∀ ab, uniformInput n ab = if ab.2 then 0 else
        (((2 : ℝ)^(-(n : ℝ)/2) : ℝ) : ℂ))

abbrev arena : Arena := ⟨signature, sourceLaw⟩

private theorem rejected_law : ¬ sourceLaw rejected := by
  intro h
  have h₀ := h 0 0 (by norm_num) (by norm_num) (fun _ => false)
  rcases h₀ with ⟨_, _, _, _, _, _, _, _, hu, _⟩
  norm_num [rejected, realize, minimumFidelity] at hu

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0, fun _ => false⟩, (fun _ => 0), uniformInput 0, ?_⟩
  intro h
  change squaredFidelity 0 0 (fun _ => false) (fun _ => 0) =
    squaredFidelity 0 0 (fun _ => false) (uniformInput 0) at h
  have hz : squaredFidelity 0 0 (fun _ => false) (fun _ => 0) = 0 := by
    simp [squaredFidelity, idealOutput]
  have hu := result 0 0 (by norm_num) (by norm_num) (fun _ => false)
  rcases hu with ⟨_, _, _, _, _, _, _, _, hu, _⟩
  rw [hz, hu] at h
  norm_num [minimumFidelity] at h

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity sourceLaw actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    result (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p ψ => squaredFidelity p.1 p.2.1 p.2.2 ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannRouterDephasing
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Routing.HannRouterDephasing
