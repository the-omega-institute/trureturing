import D5.S0.Certificates.Games.SplythoffGrundyRows
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S0.Certificates.Games.SplythoffGrundyRows
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Certificates.Games.SplythoffGrundyRows
noncomputable section
private abbrev pairSignature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
private abbrev pairActual (f : ℕ × ℕ → ℕ) : Realization pairSignature :=
  realize pairSignature (fun _ _ p => f p) (fun e => nomatch e)
private abbrev pairArena (law : (ℕ × ℕ → ℕ) → Prop) : Arena where
  signature := pairSignature
  Law r := law (r.readout () ())
private def boundLaw (f : ℕ × ℕ → ℕ) : Prop :=
  ∀ x g : ℕ, ∃ y, f (x,y) = g ∧ y ≤ 5*x+2*g+3
private def rowsLaw (f : ℕ × ℕ → ℕ) : Prop :=
  (∀ x g : ℕ, ∃! y, f (x,y) = g) ∧ (∀ y g : ℕ, ∃! x, f (x,y) = g)
private def pairEvidence (f bad : ℕ × ℕ → ℕ) (law : (ℕ × ℕ → ℕ) → Prop)
    (good : law f) (rejected : ¬ law bad) (dep : ∃ p q, f p ≠ f q) :
    Registration (pairArena law) (law f) where
  actual := pairActual f
  bridge := Iff.rfl
  variation := ⟨good,pairActual bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pairActual bad,?_,rfl,rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨p,q,h⟩ := dep
    exact ⟨(),p,q,h⟩
private theorem pair_dependence : ∃ p q : ℕ × ℕ, grundy p.1 p.2 ≠ grundy q.1 q.2 := by
  obtain ⟨a,ha,_⟩ := row_exists_bound 0 0
  obtain ⟨b,hb,_⟩ := row_exists_bound 0 1
  exact ⟨(0,a),(0,b),by simp only [ha,hb]; decide⟩
private theorem bound_bad : ¬ boundLaw (fun _ => 0) := by
  intro h
  obtain ⟨y,hy,_⟩ := h 0 1
  exact Nat.zero_ne_one hy
private theorem rows_bad : ¬ rowsLaw (fun _ => 0) := by
  intro h
  obtain ⟨y,hy,_⟩ := h.1 0 1
  exact Nat.zero_ne_one hy
private def bound_evidence : Registration (pairArena boundLaw)
    (∀ x g : ℕ, ∃ y, grundy x y = g ∧ y ≤ 5*x+2*g+3) :=
  pairEvidence (fun p => grundy p.1 p.2) (fun _ => 0) boundLaw
    row_exists_bound bound_bad pair_dependence
private def rows_evidence : Registration (pairArena rowsLaw) claim :=
  pairEvidence (fun p => grundy p.1 p.2) (fun _ => 0) rowsLaw
    result rows_bad pair_dependence
noncomputable def bound_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S0.Certificates.Games.SplythoffGrundyRows.row_exists_bound)
    (Realization pairSignature) Unit Unit := {
  unitName := `Reg.D5.S0.Certificates.Games.SplythoffGrundyRows.bound_unit
  realizationName := ``bound_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena boundLaw⟩
  objectArena := .source ⟨pairArena boundLaw⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (pairArena boundLaw) ⟨bound_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ _ p => grundy p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
noncomputable def result_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S0.Certificates.Games.SplythoffGrundyRows.result)
    (Realization pairSignature) Unit Unit := {
  unitName := `Reg.D5.S0.Certificates.Games.SplythoffGrundyRows.result_unit
  realizationName := ``rows_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena rowsLaw⟩
  objectArena := .source ⟨pairArena rowsLaw⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (pairArena rowsLaw) ⟨rows_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ _ p => grundy p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S0.Certificates.Games.SplythoffGrundyRows
