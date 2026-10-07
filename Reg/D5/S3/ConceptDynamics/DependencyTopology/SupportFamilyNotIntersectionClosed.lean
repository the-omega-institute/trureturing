import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed
import Reg.Support.DependentFamily

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.DependencyTopology
open LegalLedgerFixedSet SupportFamilyNotIntersectionClosed

namespace Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed

noncomputable section

abbrev signature : Signature where
  Params := Σ _P : Type, Σ _Proof : Type, Σ _Ax : Type, Type
  State p := KernelData p.1 p.2.1 p.2.2.1 p.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (Set p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => supportFamily k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ¬ (∀ (P Proof Ax Model : Type) (k : KernelData P Proof Ax Model), SourceLaws k →
    IntersectionClosed (R.readout () ⟨P, Proof, Ax, Model⟩ k) ∨
      ∃ edge : P → P → Prop, supportFamily k = graphFamily edge)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro P Proof Ax Model k laws
  exact Or.inl (fun _ _ _ _ => Set.mem_univ _)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let none : KernelData Unit Unit Unit Unit :=
    (fun _ _ => false, fun _ => ∅, fun _ => ∅, ∅, id, fun _ _ => True, fun _ _ => True)
  let some : KernelData Unit Unit Unit Unit :=
    (fun _ _ => true, fun _ => ∅, fun _ => ∅, ∅, id, fun _ _ => True, fun _ _ => True)
  refine ⟨⟨Unit, Unit, Unit, Unit⟩, none, some, ?_⟩
  intro heq
  have good : ({()} : Set Unit) ∈ supportFamily some := by
    refine ⟨⟨⟨{()}, fun _ => ()⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p; rfl
    · intro p ax h; exact Finset.notMem_empty ax h
    · intro p q h; exact (Finset.notMem_empty q h).elim
    · intro p h
      have impossible : Relation.TransGen (fun _ _ : Unit => False) p p :=
        Relation.TransGen.mono (by rintro _ _ ⟨_, h⟩; exact Finset.notMem_empty _ h) p p h
      simpa only [Relation.transGen_eq_self] using impossible
    · simp [CertifiedNodes.nodes]
  have bad : ({()} : Set Unit) ∉ supportFamily none := by
    rintro ⟨C, hC⟩
    have hp : () ∈ C.nodes := by
      change () ∈ (↑C.nodes : Set Unit)
      rw [hC]
      exact Set.mem_singleton ()
    have h := C.property.1 ⟨(), hp⟩
    exact Bool.false_ne_true h
  change supportFamily none = supportFamily some at heq
  exact bad (heq ▸ good)

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i
      cases j
      exact False.elim (h rfl)
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.result) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ _ k => supportFamily.{0, 0, 0, 0} k) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "DependencyTopology") "SupportFamilyNotIntersectionClosed") "result") "Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed/Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ _ k => supportFamily.{0, 0, 0, 0} k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, definition := some { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, name := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.claim, path := #["arg"] }, coordinates := #[0, 1, 2, 3], readouts := #[{ path := #["arg", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.anchorEnumeration }


end

end Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed


noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.arena
noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.arena
noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.arena) (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.observation0 : (P Proof Ax Model : Type) →
  (k : D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet.KernelData.{0, 0, 0, 0} P Proof Ax Model) →
    @D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet.SourceLaws.{0, 0, 0, 0} P Proof Ax Model k →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
        Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.signature PUnit.unit.{1}
        (@Sigma.mk.{1, 1} Type
          (fun (_P : Type) => @Sigma.{1, 1} Type fun (_Proof : Type) => @Sigma.{1, 1} Type fun (_Ax : Type) => Type) P
          (@Sigma.mk.{1, 1} Type (fun (_Proof : Type) => @Sigma.{1, 1} Type fun (_Ax : Type) => Type) Proof
            (@Sigma.mk.{1, 1} Type (fun (_Ax : Type) => Type) Ax Model))) :=
  fun (P Proof Ax Model : Type)
    (k : D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet.KernelData.{0, 0, 0, 0} P Proof Ax Model)
    (a : @D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet.SourceLaws.{0, 0, 0, 0} P Proof Ax Model k) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.signature
    Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.actual PUnit.unit.{1}
    (@Sigma.mk.{1, 1} Type
      (fun (_P : Type) => @Sigma.{1, 1} Type fun (_Proof : Type) => @Sigma.{1, 1} Type fun (_Ax : Type) => Type) P
      (@Sigma.mk.{1, 1} Type (fun (_Proof : Type) => @Sigma.{1, 1} Type fun (_Ax : Type) => Type) Proof
        (@Sigma.mk.{1, 1} Type (fun (_Ax : Type) => Type) Ax Model)))
    k

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.claim, part := .value, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration).actual (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration).variation.1 (Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"DependencyTopology\",\"SupportFamilyNotIntersectionClosed\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed, declaration := `Reg.D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
