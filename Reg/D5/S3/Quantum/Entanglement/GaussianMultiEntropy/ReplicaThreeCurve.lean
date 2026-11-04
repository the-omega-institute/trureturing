import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
import Reg.Support.SingleDependentReadout

/-! Complete-law source-bound audit attempts for the labelled curve. -/
namespace Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Derivative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p b => deriv (curve p.1 p.2) b) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,6⟩, 1, 2, ?_⟩
  have hn := (curve_derivative 1 6 1 (by norm_num) (by norm_num) (by norm_num)).2.1.mpr
    (by norm_num)
  have hz := (curve_derivative 1 6 2 (by norm_num) (by norm_num) (by norm_num)).2.2.1.mpr
    (by norm_num)
  change deriv (curve 1 6) 1 ≠ deriv (curve 1 6) 2
  rw [hz]
  exact hn.ne
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k N b : ℝ), 0 < k → 0 < N → b ∈ Ioo 0 (N / 2) →
    HasDerivAt (curve k N) (curveDerivative k N b) b ∧
    (R.readout () ⟨k,N⟩ b < 0 ↔ b < N / 3) ∧
    (deriv (curve k N) b = 0 ↔ b = N / 3) ∧
    (0 < deriv (curve k N) b ↔ N / 3 < b)
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := (h 1 6 1 (by norm_num) (by norm_num) (by norm_num)).2.1.mpr (by norm_num)
  norm_num [zeroReadout, realize] at he
def family : Registration arena (type_of% @curve_derivative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨curve_derivative, zeroReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@curve_derivative) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Derivative.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => deriv (curve p.1 p.2) b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Derivative

namespace Minimum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p b => curve p.1 p.2 b) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,6⟩, 1, 2, ?_⟩
  have h := (curve_minimum 1 6 (by norm_num) (by norm_num)).1
    (show (1 : ℝ) ∈ Ioc 0 (6 / 3) by norm_num)
    (show (2 : ℝ) ∈ Ioc 0 (6 / 3) by norm_num) (by norm_num)
  exact ne_of_gt h
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k N : ℝ), 0 < k → 0 < N →
    StrictAntiOn (R.readout () ⟨k,N⟩) (Ioc 0 (N / 3)) ∧
    StrictMonoOn (curve k N) (Ico (N / 3) (N / 2)) ∧
    ∀ b ∈ Ioo 0 (N / 2), curve k N (N / 3) ≤ curve k N b ∧
      (curve k N b = curve k N (N / 3) ↔ b = N / 3)
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := (h 1 6 (by norm_num) (by norm_num)).1
    (show (1 : ℝ) ∈ Ioc 0 (6 / 3) by norm_num)
    (show (2 : ℝ) ∈ Ioc 0 (6 / 3) by norm_num) (by norm_num)
  norm_num [zeroReadout, realize] at he
def family : Registration arena (type_of% @curve_minimum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨curve_minimum, zeroReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@curve_minimum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Minimum.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Minimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => curve p.1 p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Minimum

namespace Boundary
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p b => curve p.1 p.2 b) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,6⟩, 1, 2, ?_⟩
  have h := (curve_minimum 1 6 (by norm_num) (by norm_num)).1
    (show (1 : ℝ) ∈ Ioc 0 (6 / 3) by norm_num)
    (show (2 : ℝ) ∈ Ioc 0 (6 / 3) by norm_num) (by norm_num)
  exact ne_of_gt h
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k N : ℝ), 0 ≤ k → 0 < N →
    curve k N 0 = 0 ∧ curve k N (N / 2) = 0 ∧
    Tendsto (R.readout () ⟨k,N⟩) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (curve k N) (𝓝[<] (N / 2)) (𝓝 0) ∧
    (∀ b : ℝ, curve 0 N b = 0)
private theorem rejected : ¬ arena.Law oneReadout := by
  intro h
  have ht := (h 1 6 (by norm_num) (by norm_num)).2.2.1
  change Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 0) at ht
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique hc ht
  norm_num at he
def family : Registration arena (type_of% @curve_boundaries) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨curve_boundaries, oneReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@curve_boundaries) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Boundary.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Boundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => curve p.1 p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Boundary

namespace Physical
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p b => GM3 3 (p.1 - 2 * p.2) p.2 p.2 b) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3,1⟩, 1, 2, ?_⟩
  have h := (GM3_three_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2.1
    (show (1 : ℝ) ∈ Ici 1 by norm_num)
    (show (2 : ℝ) ∈ Ici 1 by norm_num) (by norm_num)
  exact ne_of_gt h
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), 3 ≤ N → 3 ∣ N → ∀ (a : ℝ), 1 < a →
      ∀ (b : ℕ), 0 < b → 2 * b < N →
    R.readout () ⟨N,b⟩ a = curve (kappa N a) N b ∧
    GM3 3 (N / 3) (N / 3) (N / 3) a ≤ GM3 3 (N - 2 * b) b b a ∧
    (GM3 3 (N - 2 * b) b b a = GM3 3 (N / 3) (N / 3) (N / 3) a ↔ b = N / 3) ∧
    (b = N / 3 ↔ (b : ℝ) + b = 2 * (N : ℝ) / 3)
private theorem rejected : ¬ arena.Law oneReadout := by
  intro h
  have he := (h 3 (by norm_num) (by norm_num) 2 (by norm_num) 1
    (by norm_num) (by norm_num)).1
  norm_num [oneReadout, realize] at he
  have hn := value_neg (kappa 3 2) 1 1 1 (by norm_num [kappa])
    (by norm_num) (by norm_num) (by norm_num)
  norm_num only [curve, show (3 : ℝ) - 2 * 1 = 1 by norm_num] at he
  linarith
def family : Registration arena (type_of% @physical_curve_minimum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_curve_minimum, oneReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_curve_minimum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Physical.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.Physical.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => GM3 3 (p.1 - 2 * p.2) p.2 p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
    definition := none
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Physical

end
end Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
