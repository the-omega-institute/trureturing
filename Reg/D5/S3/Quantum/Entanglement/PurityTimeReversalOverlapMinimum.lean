import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
open _root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State N := (Fin N → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => ∑ w, ‖ψ w‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original claim; only the norm `∑ w, ‖ψ w‖ ^ 2` in the hypothesis of the lower
bound is replaced by the readout. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (A : Finset (Fin N)), 1 ≤ A.card → A.card < N →
    (∀ ψ : (Fin N → Fin 2) → ℂ, O.readout () N ψ = 1 →
      conjecturedMin N A.card ≤ purityPlusOverlap A ψ) ∧
    ∃ ψ : (Fin N → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 ∧
      purityPlusOverlap A ψ = conjecturedMin N A.card

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 2 {0} (by decide) (by decide)).1 0 rfl
  have hz : purityPlusOverlap ({0} : Finset (Fin 2)) 0 = 0 := by
    have h0' : reducedState ({0} : Finset (Fin 2)) 0 = 0 := by
      ext x y
      simp [reducedState, partialTraceRight]
    simp [purityPlusOverlap, h0', timeReversed]
  rw [hz] at h0
  have hpos : (0 : ℝ) < conjecturedMin 2 ({0} : Finset (Fin 2)).card := by
    unfold conjecturedMin; split_ifs <;> positivity
  linarith

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, fun _ => 0, fun _ => 1, fun h => ?_⟩
  change (∑ w : Fin 0 → Fin 2, ‖(0 : ℂ)‖ ^ 2) = ∑ w : Fin 0 → Fin 2, ‖(1 : ℂ)‖ ^ 2 at h
  simp at h

def registration :
    Registration arena
      _root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ψ => ∑ w, ‖ψ w‖ ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "PurityTimeReversalOverlapMinimum") "result") "Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum/Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ψ => ∑ w, ‖ψ w‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, definition := some { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, name := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.claim, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body", "domain", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum


noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.arena) (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration).actual

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.observation0 : (N : Nat) →
  (A : Finset.{0} (Fin N)) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Finset.card.{0} (Fin N) A) →
      @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin N) A) N →
        (ψ : (Fin N → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) → Complex) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.signature PUnit.unit.{1} N :=
  fun (N : Nat) (A : Finset.{0} (Fin N))
    (a :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Finset.card.{0} (Fin N) A))
    (a_1 : @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin N) A) N)
    (ψ : (Fin N → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) → Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.signature
    Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.actual PUnit.unit.{1} N ψ

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.claim, part := .value, path := [.body, .body, .body, .body, .function, .argument, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration).actual (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration).variation.1 (Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PurityTimeReversalOverlapMinimum\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum, declaration := `Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
