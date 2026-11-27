import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

open scoped Quaternion
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

namespace Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ M : ℕ, Fin M → ℍ[ℤ])
    (fun p => Fin p.1) (fun _ => ℍ[ℤ])

def actual : Realization signature :=
  realize signature (fun _ p r => p.2 r) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {M : ℕ} (hM : 2 ≤ M) (s : Fin M → ℍ[ℤ]),
    (∀ r, IsQ8 (O.readout () ⟨M, s⟩ r)) → ∀ (u : ℍ[ℤ]) (hu : Noncentral u),
    ∃ τ : ℤ, 0 < τ ∧ τ < (M : ℤ) ∧ ¬ ((M : ℤ) ∣ τ) ∧
      correlation (by omega) s u hu τ ≠ 0

private theorem constantOne_fails : ¬ arena.Law constantOne := by
  intro h
  let u : ℍ[ℤ] := ⟨0, 1, 0, 0⟩
  have hu : Noncentral u := Or.inl rfl
  obtain ⟨τ, _, _, _, hτ⟩ := h (M := 2) le_rfl (fun _ => 0) (fun _ => Or.inl rfl) u hu
  exact hτ (by simp [correlation])

private theorem actual_depends_on_index : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, fun r => if r = 0 then 1 else -1⟩, 0, 1, ?_⟩
  intro h
  have hr := congrArg QuaternionAlgebra.re h
  change (1 : ℤ) = -1 at hr
  omega

/-- A constant unit readout accepts the zero sequence, whose literal correlations all vanish. -/
def family : Registration arena (type_of% @blake_conjecture_5_2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@blake_conjecture_5_2, constantOne, constantOne_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantOne constantOne_fails
  dependence := actual_depends_on_index

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@blake_conjecture_5_2) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52.blake_conjecture_5_2.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p r => p.2 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52
