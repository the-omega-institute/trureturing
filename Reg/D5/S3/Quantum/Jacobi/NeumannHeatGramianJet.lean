import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
import Reg.Support.SingleDependentReadout

/-! The reveal degree is an essential readout in the nonvanishing assertion. -/

namespace Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ k => 2 * k + 2) (fun e => nomatch e)

def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (p q : Path n) (k : ℕ) (c e : ℝ),
    0 < k → k < n → (∀ i < k, p.edge i = q.edge i) → p.edge k ≠ q.edge k →
    (∀ d < 2 * k + 2, coeff d (gramian (p.heat c) - gramian (q.heat e)) = 0) ∧
    coeff (2 * k + 2) (gramian (p.heat c) - gramian (q.heat e)) =
      -(p.moment 1) * (2 * k : ℕ) * (p.moment (2 * k) - q.moment (2 * k)) /
        (((2 * k + 2 : ℕ).factorial : ℝ)) ∧
    coeff (R.readout () () k) (gramian (p.heat c) - gramian (q.heat e)) ≠ 0

private def twoCells (a : ℝ) (ha : 0 < a) : Path 2 where
  length i := if i.val = 0 then 1 else a
  positive i := by split <;> positivity

private theorem discarded_fails : ¬ arena.Law discarded := by
  intro law
  let p := twoCells 2 (by norm_num)
  let q := twoCells 3 (by norm_num)
  have hp : ∀ i < 1, p.edge i = q.edge i := by
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [p, q, twoCells, Path.edge]
  have hne : p.edge 1 ≠ q.edge 1 := by norm_num [p, q, twoCells, Path.edge]
  have h := (law p q 1 0 0 (by decide) (by decide) hp hne).2.2
  change coeff 0 (gramian (p.heat 0) - gramian (q.heat 0)) ≠ 0 at h
  exact h (by simp [gramian])

def family : Registration arena (type_of% @first_reveal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_reveal, discarded, discarded_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (1 : ℕ), (2 : ℕ), by change 4 ≠ (6 : ℕ); decide⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_reveal) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianJet.unit
  realizationName := `Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianJet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => 2 * k + 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
