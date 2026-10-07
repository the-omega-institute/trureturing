import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : CountMat n n} {Q : Type},
    [Fintype Q] → ∀ (L : IncomingLift A Q),
    let D := differenceSpace L.project
    let T := edgeLinear L
    let W := imageChain T D
    D = LinearMap.ker (Finsupp.lmapDomain ℚ ℚ L.project) ∧
    Module.finrank ℚ D = Fintype.card Q - R.readout () () n ∧
    (∀ a, D.map (T a) ≤ D) ∧
    (∀ (w : List (Edge A)),
      (∀ (i j : Fin n) (p : FinitePath A w.length i j), pathWord p ≠ w) →
      wordOperator T w = 0) ∧
    (∀ d, Forgets L d ↔ ∀ w : List (Edge A), w.length = d →
      D.map (wordOperator T w) = ⊥) ∧
    (∀ w : List (Edge A), D.map (wordOperator T w) = ⊥ ↔
      (wordOperator T w).domRestrict D = 0) ∧
    (∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j),
      (pathWord p).length = d ∧
      ∀ u : {q : Q // L.project q = j},
        wordOperator T (pathWord p) (Finsupp.single u.val 1) =
          Finsupp.single (L.liftPath p u).val 1) ∧
    W 0 = D ∧
    (∀ j, W (j + 1) = ⨆ a, (W j).map (T a)) ∧
    (∀ j, W j = ⨆ w : {w : List (Edge A) // w.length = j},
      D.map (wordOperator T w.val)) ∧
    (∀ j, W (j + 1) ≤ W j) ∧
    (∀ j, W (j + 1) = W j → ∀ k, W (j + k) = W j) ∧
    (∀ d, Forgets L d ↔ W d = ⊥) ∧
    (∀ d, IsLeast {j | Forgets L j} d ↔ IsLeast {j | W j = ⊥} d) ∧
    ((∃ d, Forgets L d) → ∃ d ≤ Fintype.card Q - n, IsLeast {j | Forgets L j} d) ∧
    ((∃ d, Forgets L d) ↔ W (Fintype.card Q - n) = ⊥) ∧
    (∃ L₀ : IncomingLift (fun (_ _ : Fin 1) => 2) Bool,
      (∀ u, (L₀.lift ⟨0, 0, 0⟩ u).val = u.val) ∧
      (∀ u, (L₀.lift ⟨0, 0, 1⟩ u).val = !u.val) ∧
      ((1 / 2 : ℚ) • (edgeLinear L₀ ⟨0, 0, 0⟩ + edgeLinear L₀ ⟨0, 0, 1⟩)).domRestrict
        (differenceSpace L₀.project) = 0 ∧
      ∀ d, ¬ Forgets L₀ d)

theorem actual_law : arena.Law actual := by
  intro n A Q inst L
  exact common_nilpotency_forgetting_bound L

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A : CountMat 1 1 := fun _ _ => 1
  let L : IncomingLift A Bool := {
    project := fun _ => 0
    onto := by intro v; exact ⟨false, Subsingleton.elim _ _⟩
    lift := fun _ _ => ⟨false, Subsingleton.elim _ _⟩ }
  have htrue := (common_nilpotency_forgetting_bound L).2.1
  have hfalse := (h L).2.1
  change Module.finrank ℚ (differenceSpace L.project) =
    Fintype.card Bool - (1 + 1) at hfalse
  change Module.finrank ℚ (differenceSpace L.project) = Fintype.card Bool - 1 at htrue
  norm_num only [Fintype.card_bool, Nat.reduceAdd, Nat.reduceSub] at hfalse htrue
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.common_nilpotency_forgetting_bound) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CommonNilpotencyForgettingBound") "common_nilpotency_forgetting_bound") "Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound/Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.common_nilpotency_forgetting_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.arena) (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"common_nilpotency_forgetting_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.common_nilpotency_forgetting_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.observation0 : {n : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {Q : Type} →
      [Fintype.{0} Q] →
        (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift n A Q) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {n : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} {Q : Type} [Fintype.{0} Q]
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift n A Q) =>
  have D :
    @Submodule.{0, 0} Rat
      (@Finsupp.{0, 0} Q Rat (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)))
      Rat.semiring (@Finsupp.instAddCommMonoid.{0, 0} Q Rat Rat.addCommMonoid)
      (@Finsupp.module.{0, 0, 0} Q Rat Rat Rat.semiring Rat.addCommMonoid (@Semiring.toModule.{0} Rat Rat.semiring)) :=
    @D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.differenceSpace.{0, 0} Q (Fin n)
      (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project n A Q L);
  have T :
    (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n A) →
      @LinearMap.{0, 0, 0, 0} Rat Rat Rat.semiring Rat.semiring
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring))
        (@Finsupp.{0, 0} Q Rat (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)))
        (@Finsupp.{0, 0} Q Rat (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)))
        (@Finsupp.instAddCommMonoid.{0, 0} Q Rat Rat.addCommMonoid)
        (@Finsupp.instAddCommMonoid.{0, 0} Q Rat Rat.addCommMonoid)
        (@Finsupp.module.{0, 0, 0} Q Rat Rat Rat.semiring Rat.addCommMonoid (@Semiring.toModule.{0} Rat Rat.semiring))
        (@Finsupp.module.{0, 0, 0} Q Rat Rat Rat.semiring Rat.addCommMonoid
          (@Semiring.toModule.{0} Rat Rat.semiring)) :=
    @D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.edgeLinear n A Q L;
  have W :
    Nat →
      @Submodule.{0, 0} Rat
        (@Finsupp.{0, 0} Q Rat (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)))
        (@DivisionSemiring.toSemiring.{0} Rat
          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
        (@AddCommGroup.toAddCommMonoid.{0}
          (@Finsupp.{0, 0} Q Rat (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)))
          (@Finsupp.instAddCommGroup.{0, 0} Q Rat Rat.addCommGroup))
        (@Finsupp.module.{0, 0, 0} Q Rat Rat Rat.semiring Rat.addCommMonoid
          (@Semiring.toModule.{0} Rat Rat.semiring)) :=
    @D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.imageChain.{0, 0, 0} Rat
      (@Finsupp.{0, 0} Q Rat (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)))
      (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n A) Rat.instField
      (@Finsupp.instAddCommGroup.{0, 0} Q Rat Rat.addCommGroup)
      (@Finsupp.module.{0, 0, 0} Q Rat Rat Rat.semiring Rat.addCommMonoid (@Semiring.toModule.{0} Rat Rat.semiring)) T
      D;
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.signature
    Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"common_nilpotency_forgetting_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.common_nilpotency_forgetting_bound, part := .type, path := [.body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .argument, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"common_nilpotency_forgetting_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.common_nilpotency_forgetting_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CommonNilpotencyForgettingBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
