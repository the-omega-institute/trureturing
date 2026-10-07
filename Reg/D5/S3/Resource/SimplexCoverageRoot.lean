import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.SimplexCoverageRoot
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Resource.SimplexCoverageRoot

open _root_.D5.S3.Resource.SimplexCoveragePolynomial
open _root_.D5.S3.Resource.SimplexCoverageRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

universe w u v

namespace Line

private abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ value => value) (fun impossible => nomatch impossible)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {Index : Type w} [Fintype Index]
    (polynomial : MvPolynomial Index ℚ) (x y : Index → ℝ) (time : ℝ),
    HasDerivAt (fun parameter => evaluateAt (fun index => x index + parameter * y index)
      polynomial)
      (observation.readout () () (∑ index, y index *
        evaluateAt (fun index => x index + time * y index) (MvPolynomial.pderiv index polynomial)))
      time

private theorem actualLaw : arena.{w}.Law actual := @evaluateAt_line_hasDerivAt

private theorem rejectedLaw : ¬ arena.{w}.Law rejected := by
  intro law
  have derivative := law (Index := ULift.{w} Unit) 0 (fun _ => 0) (fun _ => 0) 0
  have zero_derivative : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 1 0 := by
    simpa [rejected, realize, evaluateAt] using derivative
  have contradiction := zero_derivative.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  norm_num at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

private def registration : Registration arena.{w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.SimplexCoverageRoot.evaluateAt_line_hasDerivAt.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ value => value)
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "SimplexCoverageRoot") "evaluateAt_line_hasDerivAt") "Reg.D5.S3.Resource.SimplexCoverageRoot/_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "SimplexCoverageRoot") 0) "Reg") "D5") "S3") "Resource") "SimplexCoverageRoot") "Line") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ value => value)
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.SimplexCoverageRoot, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #[], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.evaluateAt_line_hasDerivAt, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalArenaFact, `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.sourceBridgeFact, `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.observationFact0, `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.anchorEnumeration }


#print axioms registration

end Line

namespace Root

private abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ degree value => value ^ (1 / (degree : ℝ)))
    (fun impossible => nomatch impossible)

private def rejected : Realization signature :=
  realize signature (fun _ _ value => value ^ 2) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {Index : Type w} [Fintype Index] [DecidableEq Index]
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (columns : Index → V) (U : Submodule K V) [FiniteDimensional K (V ⧸ U)]
    (degree : ℕ) (_positive_degree : 1 ≤ degree),
    ConcaveOn ℝ {x : Index → ℝ | ∀ index, 0 ≤ x index}
      (fun x => observation.readout () degree (evaluateAt x (spanningPolynomial columns U degree)))

private theorem actualLaw : arena.{w,u,v}.Law actual := @spanningPolynomial_root_concaveOn

private theorem rejectedLaw : ¬ arena.{w,u,v}.Law rejected := by
  classical
  let basis : Module.Basis (Fin 0) (ULift.{u} ℚ) (ULift.{v} (Fin 0 → ℚ)) :=
    ((Pi.basisFun ℚ (Fin 0)).mapCoeffs ULift.ringEquiv.symm
      (by intro scalar vector; rfl)).map ULift.moduleEquiv.symm
  let : FiniteDimensional (ULift.{u} ℚ) (ULift.{v} (Fin 0 → ℚ)) :=
    Module.Finite.of_basis basis
  let columns : ULift.{w} Unit → ULift.{v} (Fin 0 → ℚ) := fun _ => 0
  have polynomial_identity : spanningPolynomial (K := ULift.{u} ℚ) columns ⊤ 1 =
      MvPolynomial.X (default : ULift.{w} Unit) := by
    apply MvPolynomial.ext
    intro alpha
    have singleton : Finsupp.single (default : ULift.{w} Unit) 1 = alpha ↔
        alpha default = 1 := by
      constructor
      · intro equality
        rw [← equality]
        simp
      · intro equality
        apply Finsupp.ext
        intro index
        have index_eq : index = default := Subsingleton.elim _ _
        subst index
        simpa using equality.symm
    rw [spanningPolynomial_coeff, MvPolynomial.coeff_X]
    simp only [singleton, representedSpan, top_sup_eq, Fintype.sum_unique, and_true]
    split_ifs with equality
    · simp [reciprocalFactorial, equality]
    · rfl
  intro law
  have concavity := law (K := ULift.{u} ℚ) (V := ULift.{v} (Fin 0 → ℚ))
    (Index := ULift.{w} Unit) columns ⊤ 1 (by norm_num)
  have jensen := concavity.2
  have contradiction := jensen (x := fun _ => 0) (y := fun _ => 2)
    (by intro index; norm_num) (by intro index; norm_num)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize, polynomial_identity, evaluateAt, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

private def registration : Registration arena.{w,u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

noncomputable def registration_2.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.SimplexCoverageRoot.spanningPolynomial_root_concaveOn.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ degree value => value ^ (1 / (degree : ℝ)))
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "SimplexCoverageRoot") "spanningPolynomial_root_concaveOn") "Reg.D5.S3.Resource.SimplexCoverageRoot/_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "SimplexCoverageRoot") 0) "Reg") "D5") "S3") "Resource") "SimplexCoverageRoot") "Root") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ degree value => value ^ (1 / (degree : ℝ)))
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.SimplexCoverageRoot, definition := none, coordinates := #[11], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.spanningPolynomial_root_concaveOn, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalArenaFact, `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.sourceBridgeFact, `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.observationFact0, `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.anchorEnumeration }


#print axioms registration

end Root

end Reg.D5.S3.Resource.SimplexCoverageRoot


noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.arena.{u_1}
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.arena.{u_1}
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.arena.) (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration.{u_1, u_2,
  u_3}).actual

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"spanningPolynomial_root_concaveOn\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.spanningPolynomial_root_concaveOn, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration.{u_1, u_2,
  u_3}).bridge

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.observation0.{u_1, u_2, u_3} : {Index : Type u_1} →
  [Fintype.{u_1} Index] →
    [DecidableEq.{u_1 + 1} Index] →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field.{u_2} K] →
            [inst_1 : AddCommGroup.{u_3} V] →
              [inst_2 :
                  @Module.{u_2, u_3} K V
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                    (@AddCommGroup.toAddCommMonoid.{u_3} V inst_1)] →
                (columns : Index → V) →
                  (U :
                      @Submodule.{u_2, u_3} K V
                        (@DivisionSemiring.toSemiring.{u_2} K
                          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                        (@AddCommGroup.toAddCommMonoid.{u_3} V inst_1) inst_2) →
                    [@FiniteDimensional.{u_2, u_3} K
                          (@HasQuotient.Quotient.{u_3, u_3} V
                            (@Submodule.{u_2, u_3} K V
                              (@DivisionSemiring.toSemiring.{u_2} K
                                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                              (@AddCommGroup.toAddCommMonoid.{u_3} V inst_1) inst_2)
                            (@Submodule.hasQuotient.{u_2, u_3} K V
                              (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst)) inst_1 inst_2)
                            U)
                          (@Field.toDivisionRing.{u_2} K inst)
                          (@Submodule.Quotient.addCommGroup.{u_2, u_3} K V
                            (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst)) inst_1 inst_2 U)
                          (@Submodule.Quotient.module.{u_2, u_3} K V
                            (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst)) inst_1 inst_2 U)] →
                      (degree : Nat) →
                        (positive_degree :
                            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              degree) →
                          (x : Index → Real) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                              _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.signature
                              PUnit.unit.{1} degree :=
  fun {Index : Type u_1} [inst : Fintype.{u_1} Index] [inst_1 : DecidableEq.{u_1 + 1} Index] {K : Type u_2} {V : Type u_3}
    [inst_2 : Field.{u_2} K] [inst_3 : AddCommGroup.{u_3} V]
    [inst_4 :
      @Module.{u_2, u_3} K V
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@AddCommGroup.toAddCommMonoid.{u_3} V inst_3)]
    (columns : Index → V)
    (U :
      @Submodule.{u_2, u_3} K V
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@AddCommGroup.toAddCommMonoid.{u_3} V inst_3) inst_4)
    [@FiniteDimensional.{u_2, u_3} K
        (@HasQuotient.Quotient.{u_3, u_3} V
          (@Submodule.{u_2, u_3} K V
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
            (@AddCommGroup.toAddCommMonoid.{u_3} V inst_3) inst_4)
          (@Submodule.hasQuotient.{u_2, u_3} K V (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst_2))
            inst_3 inst_4)
          U)
        (@Field.toDivisionRing.{u_2} K inst_2)
        (@Submodule.Quotient.addCommGroup.{u_2, u_3} K V
          (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst_2)) inst_3 inst_4 U)
        (@Submodule.Quotient.module.{u_2, u_3} K V (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst_2))
          inst_3 inst_4 U)]
    (degree : Nat)
    (positive_degree : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) degree)
    (x : Index → Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.signature
    _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.actual PUnit.unit.{1}
    degree
    (@D5.S3.Resource.SimplexCoveragePolynomial.evaluateAt.{u_1} Index x
      (@D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial.{u_2, u_3, u_1} K V Index inst_2 inst_3 inst_4 inst
        inst_1 columns U degree))

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"spanningPolynomial_root_concaveOn\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.spanningPolynomial_root_concaveOn, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"spanningPolynomial_root_concaveOn\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.spanningPolynomial_root_concaveOn, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration.{u_1, u_2,
  u_3}).actual (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration.{u_1, u_2,
  u_3}).variation.2.choose (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration.{u_1, u_2,
  u_3}).variation.1 (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration.{u_1, u_2,
  u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Root\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Root.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.arena.) (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"evaluateAt_line_hasDerivAt\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.evaluateAt_line_hasDerivAt, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.observation0.{u_1} : {Index : Type u_1} →
  [Fintype.{u_1} Index] →
    (polynomial : @MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring) →
      (x y : Index → Real) →
        (time : Real) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.signature
            PUnit.unit.{1} PUnit.unit.{1} :=
  fun {Index : Type u_1} [inst : Fintype.{u_1} Index] (polynomial : @MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
    (x y : Index → Real) (time : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.signature
    _private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.actual PUnit.unit.{1}
    PUnit.unit.{1}
    (@Finset.sum.{u_1, 0} Index Real Real.instAddCommMonoid (@Finset.univ.{u_1} Index inst) fun (index : Index) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (y index)
        (@D5.S3.Resource.SimplexCoveragePolynomial.evaluateAt.{u_1} Index
          (fun (index : Index) =>
            @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (x index)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) time (y index)))
          (@DFunLike.coe.{max (u_1 + 1) 1, max (u_1 + 1) 1, max (u_1 + 1) 1}
            (@Derivation.{0, u_1, u_1} Rat (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
              (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring) Rat.commSemiring
              (@AddMonoidAlgebra.commSemiring.{0, u_1} Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@Finsupp.instAddCommMonoid.{u_1, 0} Index Nat Nat.instAddCommMonoid))
              (@AddMonoidAlgebra.instAddCommMonoid.{0, u_1} Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))
              (@AddMonoidAlgebra.algebra.{0, 0, u_1} Rat Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@Algebra.id.{0} Rat Rat.commSemiring)
                (@AddCommMonoid.toAddMonoid.{u_1}
                  (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  (@Finsupp.instAddCommMonoid.{u_1, 0} Index Nat Nat.instAddCommMonoid)))
              (@Semiring.toModule.{u_1} (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
                (@CommSemiring.toSemiring.{u_1} (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
                  (@AddMonoidAlgebra.commSemiring.{0, u_1} Rat
                    (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                    (@Finsupp.instAddCommMonoid.{u_1, 0} Index Nat Nat.instAddCommMonoid))))
              (@AddMonoidAlgebra.instModule.{0, 0, u_1} Rat Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring)
                (@Semiring.toModule.{0} Rat (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))))
            (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
            (fun (x : @MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring) =>
              @MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
            (@Derivation.instFunLike.{0, u_1, u_1} Rat (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
              (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring) Rat.commSemiring
              (@AddMonoidAlgebra.commSemiring.{0, u_1} Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@Finsupp.instAddCommMonoid.{u_1, 0} Index Nat Nat.instAddCommMonoid))
              (@AddMonoidAlgebra.instAddCommMonoid.{0, u_1} Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))
              (@AddMonoidAlgebra.algebra.{0, 0, u_1} Rat Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@Algebra.id.{0} Rat Rat.commSemiring)
                (@AddCommMonoid.toAddMonoid.{u_1}
                  (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  (@Finsupp.instAddCommMonoid.{u_1, 0} Index Nat Nat.instAddCommMonoid)))
              (@Semiring.toModule.{u_1} (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
                (@CommSemiring.toSemiring.{u_1} (@MvPolynomial.{u_1, 0} Index Rat Rat.commSemiring)
                  (@AddMonoidAlgebra.commSemiring.{0, u_1} Rat
                    (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                    (@Finsupp.instAddCommMonoid.{u_1, 0} Index Nat Nat.instAddCommMonoid))))
              (@AddMonoidAlgebra.instModule.{0, 0, u_1} Rat Rat
                (@Finsupp.{u_1, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring)
                (@Semiring.toModule.{0} Rat (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))))
            (@MvPolynomial.pderiv.{0, u_1} Rat Index Rat.commSemiring index) polynomial)))

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"evaluateAt_line_hasDerivAt\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.evaluateAt_line_hasDerivAt, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"evaluateAt_line_hasDerivAt\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Resource.SimplexCoverageRoot, declaration := `D5.S3.Resource.SimplexCoverageRoot.evaluateAt_line_hasDerivAt, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration.{u_1}).actual (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration.{u_1}).variation.2.choose (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration.{u_1}).variation.1 (_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageRoot\",\"Line\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageRoot, declaration := `_private.Reg.D5.S3.Resource.SimplexCoverageRoot.0.Reg.D5.S3.Resource.SimplexCoverageRoot.Line.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
