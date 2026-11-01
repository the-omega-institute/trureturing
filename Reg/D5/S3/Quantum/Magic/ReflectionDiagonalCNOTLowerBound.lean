import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the reflection-symmetric diagonal synthesis lower bound. -/

namespace Reg.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound

open _root_.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
open _root_.D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation (Qubits)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the circuit's implemented matrix at each even wire count. -/
abbrev signature : Signature where
  Params := ℕ
  State n := List (gate (2 * n))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Qubits (2 * n)) (Qubits (2 * n)) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ circuit => circuitMatrix circuit) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the phase witness, reflection symmetry, scalar and all exact synthesis tests. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    ∃ θ : Qubits (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        r.readout () n circuit =
          c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
        2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨θ, _, hbound⟩ := h 1 (by decide)
  have hbad := hbound [] 0 (by simp [rejected, realize])
  norm_num [cnotCount] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let g : gate 2 := Sum.inl ⟨(0, 1), by decide⟩
  refine ⟨1, [], [g], ?_⟩
  change circuitMatrix [] ≠ circuitMatrix [g]
  simp only [circuitMatrix, List.foldr_nil, List.foldr_cons, Matrix.mul_one]
  intro h
  have he := congrFun (congrFun h (fun _ => true)) (fun _ => true)
  change (1 : ℂ) = (if (fun _ : Fin 2 => true) =
    Function.update (fun _ : Fin 2 => true) 0 false then 1 else 0) at he
  have hne : (fun _ : Fin 2 => true) ≠
      Function.update (fun _ : Fin 2 => true) 0 false := by
    intro hh
    have hh0 := congrFun hh 0
    simp at hh0
  rw [ite_eq_right hne] at he
  exact one_ne_zero he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ circuit => circuitMatrix circuit) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
    definition := some {
      owner := `D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
      name := `D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound.result
#print _root_.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
