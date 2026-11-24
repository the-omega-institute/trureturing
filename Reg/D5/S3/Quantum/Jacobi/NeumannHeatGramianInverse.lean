import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
import Reg.Support.SingleDependentReadout

/-! The first edge length, sparse readout degree, and full-jet cutoff are
essential observations in their respective statements. -/

namespace Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
open _root_.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
open LeanInformationAudit PowerSeries
open _root_.Reg.Support.SingleDependentReadout (sensitivity)

noncomputable section

private def twoCells (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Path 2 where
  length i := if i.val = 0 then a else b
  positive i := by split <;> assumption

private def p : Path 2 := twoCells 1 2 (by norm_num) (by norm_num)
private def q : Path 2 := twoCells 2 1 (by norm_num) (by norm_num)

private theorem pq_ne : p ≠ q := by
  intro h
  have he := congrArg (fun u : Path 2 => u.edge 0) h
  norm_num [p, q, twoCells, Path.edge] at he

namespace Cubic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Path (fun _ => ℝ)

def actual : Realization signature := realize signature (fun n _ u => u.edge 0) (fun e => nomatch e)

def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (u : Path n) (c : ℝ), 0 < n →
    (∀ d < 3, coeff d (gramian (u.heat c)) = 0) ∧
    coeff 3 (gramian (u.heat c)) = 4 / (3 * R.readout n () u ^ 6)

private theorem discarded_fails : ¬ arena.Law discarded := by
  intro law
  have hbad := (law p 0 (by decide)).2
  have hgood := (cubic_coefficient p 0 (by decide)).2
  change coeff 3 (gramian (p.heat 0)) = 4 / (3 * (0 : ℝ) ^ 6) at hbad
  rw [hbad] at hgood
  norm_num [p, twoCells, Path.edge] at hgood

def family : Registration arena (type_of% @cubic_coefficient) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_coefficient, discarded, discarded_fails⟩
  sensitivity := sensitivity arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    refine ⟨2, p, q, ?_⟩
    change p.edge 0 ≠ q.edge 0
    norm_num [p, q, twoCells, Path.edge]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cubic_coefficient) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse.Cubic.unit
  realizationName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse.Cubic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun n _ u => u.edge 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cubic

namespace Sparse

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ k => readoutDegree k) (fun e => nomatch e)

def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (u v : Path n) (c e : ℝ),
    (∑ i, u.length i = ∑ i, v.length i) →
    (∀ k, k + 1 < n →
      let d := R.readout () () k
      coeff d (gramian (u.heat c)) = coeff d (gramian (v.heat e))) → u = v

private theorem discarded_fails : ¬ arena.Law discarded := by
  intro law
  apply pq_ne
  apply law p q 0 1
  · norm_num [Fin.sum_univ_two, p, q, twoCells]
  · intro k hk
    change coeff 0 (gramian (p.heat 0)) = coeff 0 (gramian (q.heat 1))
    simp [gramian]

def family : Registration arena (type_of% @sparse_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sparse_injective, discarded, discarded_fails⟩
  sensitivity := sensitivity arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change 3 ≠ (4 : ℕ); decide⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sparse_injective) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse.Sparse.unit
  realizationName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse.Sparse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => readoutDegree k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "body", "body", "value"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sparse

namespace Cutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ n => jetCutoff n) (fun e => nomatch e)

def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (L : ℝ), 0 < L → ∀ (c e : ℝ),
    (∀ u v : Path n, (∑ i, u.length i) = L → (∑ i, v.length i) = L →
      (∀ j ≤ d, coeff j (gramian (u.heat c)) = coeff j (gramian (v.heat e))) → u = v) ↔
    R.readout () () n ≤ d

private theorem discarded_fails : ¬ arena.Law discarded := by
  intro law
  have h := (law 2 0 3 (by norm_num) 0 1).mpr Nat.le.refl
  have hc := (finite_jet_injective_iff 2 0 3 (by norm_num) 0 1).mp h
  norm_num [jetCutoff, readoutDegree] at hc

def family : Registration arena (type_of% @finite_jet_injective_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_jet_injective_iff, discarded, discarded_fails⟩
  sensitivity := sensitivity arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (2 : ℕ), (3 : ℕ), by change 3 ≠ (4 : ℕ); decide⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_jet_injective_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse.Cutoff.unit
  realizationName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse.Cutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => jetCutoff n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cutoff

end
end Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
