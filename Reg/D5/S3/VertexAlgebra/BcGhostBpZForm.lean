import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostBpZForm
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostBpZForm

namespace Reg.D5.S3.VertexAlgebra.BcGhostBpZForm

noncomputable section

abbrev signature : Signature where
  Params := Finset ℕ
  State _ := GhostFock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ sites state => topCoeff (rawBasisOperator sites state))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (sites : Finset ℕ) (state : GhostFock),
    realization.readout () sites state = eps sites * state (chi sites)

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have impossible := law ∅ (basis (chi ∅))
  change (0 : ℂ) = eps ∅ * basis (chi ∅) (chi ∅) at impossible
  simp [basis] at impossible
  exact eps_nonzero ∅ impossible.symm

def sourceWitness : Registration arena
    (∀ (sites : Finset ℕ) (state : GhostFock),
      topCoeff (rawBasisOperator sites state) = eps sites * state (chi sites)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rawBasis_coeff, rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨∅, basis (chi ∅), 0, ?_⟩
    change topCoeff (rawBasisOperator ∅ (basis (chi ∅))) ≠
      topCoeff (rawBasisOperator ∅ 0)
    rw [rawBasis_coeff, rawBasis_coeff]
    simpa [basis] using eps_nonzero ∅

def rawBasis_coeff_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostBpZForm.rawBasis_coeff)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostBpZForm.rawBasis_coeff.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostBpZForm.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ sites state => topCoeff (rawBasisOperator sites state))
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostBpZForm
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms sourceWitness
#print axioms rawBasis_coeff_registration

end
end Reg.D5.S3.VertexAlgebra.BcGhostBpZForm
