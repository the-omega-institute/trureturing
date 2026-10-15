import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostRelativeForm
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostNumber
open _root_.D5.S3.VertexAlgebra.BcGhostBpZForm
open _root_.D5.S3.VertexAlgebra.BcGhostRelativeForm

namespace Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm

noncomputable section

private def nativeVacuum : Relative := ⟨basis ∅, by
  change b 0 (basis ∅) = 0
  simp [b, annihilate, annihilateBasis, basis]⟩

private theorem nativeVacuum_nonzero : nativeVacuum ≠ 0 := by
  intro equality
  have impossible := congrArg (fun state : Relative => (state : GhostFock) ∅) equality
  norm_num [nativeVacuum, basis] at impossible

private def oneWitness : RelativeDegreeOne := ⟨basis {1}, by
  constructor
  · change b 0 (basis {1}) = 0
    simp [b, annihilate, annihilateBasis, basis]
  · intro sites member
    have same : sites = {1} := by simpa [basis] using member
    rw [same]
    change degree {1} = 1
    decide⟩

private theorem oneWitness_nonzero : oneWitness ≠ 0 := by
  intro equality
  have impossible := congrArg (fun state : RelativeDegreeOne => (state : GhostFock) {1}) equality
  norm_num [oneWitness, basis] at impossible

private theorem positiveTest {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (form : Space →ₗ[ℂ] (Space →ₗ[ℂ] ℂ))
    (radical : LinearMap.ker form = ⊥) (state : Space) (nonzero : state ≠ 0) :
    ∃ other : Space, form state other ≠ 0 := by
  classical
  by_contra missing
  have vanishing : ∀ other : Space, form state other = 0 := by
    simpa only [not_exists, not_not] using missing
  have kernel : form state = 0 := by ext other; exact vanishing other
  exact nonzero ((LinearMap.ker_eq_bot'.mp radical) state kernel)

abbrev formSignature (space : Submodule ℂ GhostFock) : Signature where
  Params := space
  State _ := space
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def formActual (space : Submodule ℂ GhostFock)
    (form : space →ₗ[ℂ] (space →ₗ[ℂ] ℂ)) : Realization (formSignature space) :=
  realize (formSignature space) (fun _ first second => form first second)
    (fun empty => nomatch empty)

def formRejected (space : Submodule ℂ GhostFock) : Realization (formSignature space) :=
  realize (formSignature space) (fun _ _ _ => 0) (fun empty => nomatch empty)

abbrev radicalArena (space : Submodule ℂ GhostFock) : Arena where
  signature := formSignature space
  Law realization :=
    (∀ first : space, (∀ second : space, realization.readout () first second = 0) → first = 0) ∧
    (∀ second : space, (∀ first : space, realization.readout () first second = 0) → second = 0)

private theorem radicalBridge (space : Submodule ℂ GhostFock)
    (form : space →ₗ[ℂ] (space →ₗ[ℂ] ℂ)) :
    (radicalArena space).Law (formActual space form) ↔
      LinearMap.ker form = ⊥ ∧ LinearMap.ker form.flip = ⊥ := by
  change ((∀ first : space, (∀ second : space, form first second = 0) → first = 0) ∧
    (∀ second : space, (∀ first : space, form first second = 0) → second = 0)) ↔ _
  simp only [LinearMap.ker_eq_bot', LinearMap.ext_iff, LinearMap.zero_apply,
    LinearMap.flip_apply]

private theorem radicalRejectedFails (space : Submodule ℂ GhostFock)
    (witness : space) (nonzero : witness ≠ 0) :
    ¬ (radicalArena space).Law (formRejected space) := by
  intro law
  exact nonzero (law.1 witness (fun _ => rfl))

def radicalWitness (space : Submodule ℂ GhostFock)
    (form : space →ₗ[ℂ] (space →ₗ[ℂ] ℂ))
    (radicals : LinearMap.ker form = ⊥ ∧ LinearMap.ker form.flip = ⊥)
    (witness : space) (nonzero : witness ≠ 0) :
    Registration (radicalArena space)
      (LinearMap.ker form = ⊥ ∧ LinearMap.ker form.flip = ⊥) where
  actual := formActual space form
  bridge := (radicalBridge space form).symm
  variation := ⟨(radicalBridge space form).mpr radicals,
    formRejected space, radicalRejectedFails space witness nonzero⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨formRejected space, ?_, rfl, radicalRejectedFails space witness nonzero⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    obtain ⟨other, positive⟩ := positiveTest form radicals.1 witness nonzero
    refine ⟨witness, other, 0, ?_⟩
    change form witness other ≠ form witness 0
    simpa using positive

def relativeRadicalWitness :=
  radicalWitness Relative relativeForm relativeForm_radicals nativeVacuum nativeVacuum_nonzero

def relativeOneRadicalWitness :=
  radicalWitness RelativeDegreeOne relativeOneForm relativeOneForm_radicals oneWitness oneWitness_nonzero

abbrev isotropySignature : Signature where
  Params := Relative
  State _ := GhostFock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def isotropyActual : Realization isotropySignature :=
  realize isotropySignature (fun _ first second => BPZ first second) (fun empty => nomatch empty)

def isotropyRejected : Realization isotropySignature :=
  realize isotropySignature (fun _ _ _ => 1) (fun empty => nomatch empty)

abbrev isotropyArena : Arena where
  signature := isotropySignature
  Law realization := ∀ first second : Relative, realization.readout () first second = 0

private theorem isotropyRejectedFails : ¬ isotropyArena.Law isotropyRejected := by
  intro law
  have impossible := law 0 0
  change (1 : ℂ) = 0 at impossible
  norm_num at impossible

def isotropyWitness : Registration isotropyArena
    (∀ first second : Relative, BPZ (first : GhostFock) (second : GhostFock) = 0) where
  actual := isotropyActual
  bridge := Iff.rfl
  variation := ⟨relative_isotropic, isotropyRejected, isotropyRejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨isotropyRejected, ?_, rfl, isotropyRejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨nativeVacuum, basis (chi ∅), 0, ?_⟩
    change BPZ (basis ∅) (basis (chi ∅)) ≠ BPZ (basis ∅) 0
    rw [BPZ_basis, BPZ_basis]
    simpa [basis] using eps_nonzero ∅

abbrev selectionSignature : Signature where
  Params := ℤ × ℤ
  State _ := Relative × Relative
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def selectionActual : Realization selectionSignature :=
  realize selectionSignature (fun _ _ pair => relativeForm pair.1 pair.2)
    (fun empty => nomatch empty)

def selectionRejected : Realization selectionSignature :=
  realize selectionSignature (fun _ _ _ => 1) (fun empty => nomatch empty)

abbrev selectionArena : Arena where
  signature := selectionSignature
  Law realization := ∀ (leftGrade rightGrade : ℤ) (first second : Relative),
    HomogeneousDegree leftGrade first → HomogeneousDegree rightGrade second →
    leftGrade + rightGrade ≠ 2 → realization.readout () (leftGrade, rightGrade) (first, second) = 0

private theorem selectionRejectedFails : ¬ selectionArena.Law selectionRejected := by
  intro law
  have homogeneousZero : HomogeneousDegree 0 (0 : GhostFock) := by
    intro sites member
    simpa using member
  have impossible := law 0 0 0 0 homogeneousZero homogeneousZero (by norm_num)
  change (1 : ℂ) = 0 at impossible
  norm_num at impossible

def selectionWitness : Registration selectionArena
    (∀ (leftGrade rightGrade : ℤ) (first second : Relative),
      HomogeneousDegree leftGrade first → HomogeneousDegree rightGrade second →
      leftGrade + rightGrade ≠ 2 → relativeForm first second = 0) where
  actual := selectionActual
  bridge := Iff.rfl
  variation := ⟨relativeForm_degree_selection, selectionRejected, selectionRejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨selectionRejected, ?_, rfl, selectionRejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    obtain ⟨other, positive⟩ := positiveTest relativeForm relativeForm_radicals.1
      nativeVacuum nativeVacuum_nonzero
    refine ⟨(0, 0), (nativeVacuum, other), (nativeVacuum, 0), ?_⟩
    change relativeForm nativeVacuum other ≠ relativeForm nativeVacuum 0
    simpa using positive

def hermitianActual : Realization (formSignature RelativeDegreeOne) :=
  realize (formSignature RelativeDegreeOne)
    (fun _ first second => relativeHermitianForm first second) (fun empty => nomatch empty)

def hermitianRejected : Realization (formSignature RelativeDegreeOne) :=
  realize (formSignature RelativeDegreeOne) (fun _ _ _ => Complex.I) (fun empty => nomatch empty)

abbrev hermitianArena : Arena where
  signature := formSignature RelativeDegreeOne
  Law realization := ∀ first second : RelativeDegreeOne,
    realization.readout () first second = star (realization.readout () second first)

private theorem hermitianRejectedFails : ¬ hermitianArena.Law hermitianRejected := by
  intro law
  have impossible := law 0 0
  change Complex.I = star Complex.I at impossible
  have imaginary := congrArg Complex.im impossible
  norm_num at imaginary

def hermitianWitness : Registration hermitianArena
    (∀ first second : RelativeDegreeOne,
      relativeHermitianForm first second = star (relativeHermitianForm second first)) where
  actual := hermitianActual
  bridge := Iff.rfl
  variation := ⟨relativeHermitianForm_hermitian, hermitianRejected, hermitianRejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨hermitianRejected, ?_, rfl, hermitianRejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    have conjugateNonzero : relativeOneConjugation oneWitness ≠ 0 := by
      intro equality
      have impossible := congrArg (fun state : RelativeDegreeOne => (state : GhostFock) {1}) equality
      norm_num [relativeOneConjugation, oneWitness, conjCoeffs, basis] at impossible
    obtain ⟨other, positive⟩ := positiveTest relativeOneForm relativeOneForm_radicals.1
      (relativeOneConjugation oneWitness) conjugateNonzero
    refine ⟨oneWitness, other, 0, ?_⟩
    change relativeOneForm (relativeOneConjugation oneWitness) other ≠
      relativeOneForm (relativeOneConjugation oneWitness) 0
    simpa using positive

def relative_isotropic_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostRelativeForm.relative_isotropic)
    (Realization isotropySignature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relative_isotropic.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm.isotropyWitness
  realizationSource := none
  generated := false
  arena := .source ⟨isotropyArena⟩
  objectArena := .source ⟨isotropyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source isotropyArena ⟨isotropyWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize isotropySignature (fun _ first second => BPZ first second)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
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

def relativeForm_radicals_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeForm_radicals)
    (Realization (formSignature Relative)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeForm_radicals.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeRadicalWitness
  realizationSource := none
  generated := false
  arena := .source ⟨radicalArena Relative⟩
  objectArena := .source ⟨radicalArena Relative⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (radicalArena Relative) ⟨relativeRadicalWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (formActual Relative relativeForm)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
    definition := some {
      owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
      name := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeForm
      path := #["fn", "arg", "fn", "arg", "arg"] }
    coordinates := #[]
    readouts := #[] }
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

def relativeForm_degree_selection_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeForm_degree_selection)
    (Realization selectionSignature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeForm_degree_selection.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm.selectionWitness
  realizationSource := none
  generated := false
  arena := .source ⟨selectionArena⟩
  objectArena := .source ⟨selectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source selectionArena ⟨selectionWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize selectionSignature (fun _ _ pair => relativeForm pair.1 pair.2)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
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

def relativeOneForm_radicals_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeOneForm_radicals)
    (Realization (formSignature RelativeDegreeOne)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeOneForm_radicals.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeOneRadicalWitness
  realizationSource := none
  generated := false
  arena := .source ⟨radicalArena RelativeDegreeOne⟩
  objectArena := .source ⟨radicalArena RelativeDegreeOne⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (radicalArena RelativeDegreeOne) ⟨relativeOneRadicalWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (formActual RelativeDegreeOne relativeOneForm)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
    definition := some {
      owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
      name := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeOneForm
      path := #["fn", "arg", "fn", "arg", "arg"] }
    coordinates := #[]
    readouts := #[] }
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

def relativeHermitianForm_hermitian_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeHermitianForm_hermitian)
    (Realization (formSignature RelativeDegreeOne)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostRelativeForm.relativeHermitianForm_hermitian.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm.hermitianWitness
  realizationSource := none
  generated := false
  arena := .source ⟨hermitianArena⟩
  objectArena := .source ⟨hermitianArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hermitianArena ⟨hermitianWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (formSignature RelativeDegreeOne)
    (fun _ first second => relativeHermitianForm first second) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostRelativeForm
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

#print axioms isotropyWitness
#print axioms relativeRadicalWitness
#print axioms relativeOneRadicalWitness
#print axioms selectionWitness
#print axioms hermitianWitness
#print axioms relative_isotropic_registration
#print axioms relativeForm_radicals_registration
#print axioms relativeForm_degree_selection_registration
#print axioms relativeOneForm_radicals_registration
#print axioms relativeHermitianForm_hermitian_registration

end
end Reg.D5.S3.VertexAlgebra.BcGhostRelativeForm
