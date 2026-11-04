import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
import Reg.Support.SingleDependentReadout

/-! Faithful source-bound attempts for every all-total extrema theorem. -/
namespace Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Integer
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Fin 3 → ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p k => value k (balanced p.1 0) (balanced p.1 1) (balanced p.1 2)) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, fun _ => 1⟩, 1, 2, ?_⟩
  have h := (parameter_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)
  simpa [actual, realize, balanced] using ne_of_gt h
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℝ), 0 < k → ∀ (N : ℕ), 3 ≤ N →
      ∀ (x : Fin 3 → ℕ), (∀ i, 0 < x i) → (∑ i, x i) = N →
    R.readout () ⟨N,x⟩ k ≤ value k (x 0) (x 1) (x 2) ∧
    value k (x 0) (x 1) (x 2) ≤ value k (extreme N 0) (extreme N 1) (extreme N 2) ∧
    (value k (x 0) (x 1) (x 2) =
      value k (balanced N 0) (balanced N 1) (balanced N 2) ↔ IsBalanced x) ∧
    (value k (x 0) (x 1) (x 2) = value k (extreme N 0) (extreme N 1) (extreme N 2) ↔
      ∃ σ : Equiv.Perm (Fin 3), x = extreme N ∘ σ)
private theorem rejected : ¬ arena.Law oneReadout := by
  intro h
  have he := (h 1 (by norm_num) 3 (by norm_num) (fun _ => 1)
    (by intro i; norm_num) (by norm_num [Fin.sum_univ_three])).1
  norm_num [oneReadout, realize] at he
  have hn := value_neg 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith
def family : Registration arena (type_of% @integer_extrema) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integer_extrema, oneReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integer_extrema) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.Integer.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.Integer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k (balanced p.1 0) (balanced p.1 1) (balanced p.1 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Integer

namespace Physical
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Fin 3 → ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p k => GM3 3 (p.2 0) (p.2 1) (p.2 2) k) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, fun _ => 1⟩, 1, 2, ?_⟩
  have h := (GM3_three_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2.1
    (show (1 : ℝ) ∈ Set.Ici 1 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 1 by norm_num) (by norm_num)
  simpa [actual, realize, balanced] using ne_of_gt h
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), 3 ≤ N → ∀ (a : ℝ), 1 < a →
      ∀ (x : Fin 3 → ℕ), (∀ i, 0 < x i) → (∑ i, x i) = N →
    value (kappa N a) (balanced N 0) (balanced N 1) (balanced N 2) ≤
      GM3 3 (x 0) (x 1) (x 2) a ∧
    R.readout () ⟨N,x⟩ a ≤ value (kappa N a) (N - 2 : ℕ) 1 1 ∧
    (GM3 3 (x 0) (x 1) (x 2) a =
      value (kappa N a) (balanced N 0) (balanced N 1) (balanced N 2) ↔ IsBalanced x) ∧
    (GM3 3 (x 0) (x 1) (x 2) a = value (kappa N a) (N - 2 : ℕ) 1 1 ↔
      ∃ σ : Equiv.Perm (Fin 3), x = extreme N ∘ σ)
private theorem rejected : ¬ arena.Law oneReadout := by
  intro h
  have he := (h 3 (by norm_num) 2 (by norm_num) (fun _ => 1)
    (by intro i; norm_num) (by norm_num [Fin.sum_univ_three])).2.1
  norm_num [oneReadout, realize] at he
  have hn := value_neg (kappa 3 2) 1 1 1 (by norm_num [kappa])
    (by norm_num) (by norm_num) (by norm_num)
  linarith
def family : Registration arena (type_of% @GM3_three_extrema) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨GM3_three_extrema, oneReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@GM3_three_extrema) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.Physical.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.Physical.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => GM3 3 (p.2 0) (p.2 1) (p.2 2) k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Physical

namespace Degeneracy
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p k => value k (balanced p 0) (balanced p 1) (balanced p 2)) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 1, 2, ?_⟩
  have h := (parameter_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)
  simpa [actual, realize, balanced] using ne_of_gt h
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℝ), 0 < k → ∀ (N : ℕ), 3 ≤ N →
    (IsBalanced (extreme N) ↔ N = 3 ∨ N = 4) ∧
    (R.readout () N k = value k (extreme N 0) (extreme N 1) (extreme N 2) ↔
      N = 3 ∨ N = 4)
private theorem rejected : ¬ arena.Law oneReadout := by
  intro h
  have he := (h 1 (by norm_num) 3 (by norm_num)).2.mpr (Or.inl rfl)
  norm_num [oneReadout, realize, extreme] at he
  have hn := value_neg 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith
def family : Registration arena (type_of% @extremal_degeneracy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨extremal_degeneracy, oneReadout, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@extremal_degeneracy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.Degeneracy.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.Degeneracy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k (balanced p 0) (balanced p 1) (balanced p 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Degeneracy

end
end Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
