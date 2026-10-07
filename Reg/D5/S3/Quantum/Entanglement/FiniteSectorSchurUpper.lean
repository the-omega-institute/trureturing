import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import Reg.Support.DependentFamily
import Reg.Support.FiniteSectorSingleton

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Sector : Type u} [Fintype Sector] [DecidableEq Sector] {spectralSize : ℕ} [Nonempty Sector] (M : Model Sector spectralSize)
    (encoding : EncodingChannels M),
    ((Matrix.of fun s t => R.readout ⟨()⟩ () (kernel M s t)).PosSemidef ∧
      (∀ s, kernel M s s = 1) ∧ (∀ s t, kernel M s t ≤ 1)) ∧
    ∃ r : Sector → ℝ, r ∈ stdSimplex ℝ Sector ∧
      spectralMinimum M = ∑ s, ∑ t, r s * r t * kernel M s t ∧
      ∀ (C : QuantumChannel Sector (TargetLocal M.d × TargetLocal M.d)),
        (∀ X : Matrix Sector Sector ℂ,
          CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
            targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
              (targetEncoding M.d)ᴴ) →
        diamondDistance C encoding.target ≤ 2 * (1 - spectralMinimum M)

theorem actual_law : arena.{u}.Law actual := by
  intro Sector _ _ spectralSize _ M encoding
  exact schur_upper M encoding

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M := Reg.Support.FiniteSectorSingleton.model (ULift.{u} Unit)
  obtain ⟨encoding, _⟩ := physical_encoding M
  have hp := (h M encoding).1.1
  have hb := hp.diag_nonneg (i := (⟨()⟩ : ULift.{u} Unit))
  change (0 : ℂ) ≤ -1 at hb
  norm_num [Complex.le_def] at hb

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

#print axioms registration

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.schur_upper.{u}) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => (x : ℂ)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteSectorChannelOptimality") "schur_upper") "Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper/Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => (x : ℂ)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "body", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.schur_upper, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.anchorEnumeration }



end Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.actual.{u})
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"schur_upper\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.schur_upper, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.arena.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.actual.{u})
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.roleEnumeration.{u} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u, 0} Unit) where
  values := [@ULift.up.{u, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.observation0.{u} : {Sector : Type u} →
  [inst : Fintype.{u} Sector] →
    [inst_1 : DecidableEq.{u + 1} Sector] →
      {spectralSize : Nat} →
        [Nonempty.{u + 1} Sector] →
          (M : @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.{u} Sector inst spectralSize) →
            (encoding :
                @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.EncodingChannels.{u} Sector inst inst_1
                  spectralSize M) →
              (s t : Sector) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u, 0, 0}
                  Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.signature.{u} (@ULift.up.{u, 0} Unit Unit.unit)
                  PUnit.unit.{1} :=
  fun {Sector : Type u} [inst : Fintype.{u} Sector] [DecidableEq.{u + 1} Sector] {spectralSize : Nat}
    [Nonempty.{u + 1} Sector]
    (M : @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.{u} Sector inst spectralSize)
    (encoding :
      @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.EncodingChannels.{u} Sector inst inst_1 spectralSize M)
    (s t : Sector) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.signature.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.actual.{u} (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1}
    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.kernel.{u} Sector inst spectralSize M s t)

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"schur_upper\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\",\"body\",\"body\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.schur_upper, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .argument, .argument, .body, .body], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"schur_upper\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.schur_upper, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration.{u}).actual (Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration.{u}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration.{u}).variation.1 (Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorSchurUpper\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
