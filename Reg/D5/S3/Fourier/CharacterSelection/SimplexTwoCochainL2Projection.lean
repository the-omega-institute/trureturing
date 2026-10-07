import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection

universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    ∀ {V : Type u} [Fintype V] [Nonempty V],
    (∀ (F : V → V → V → ℝ)
      (h12 : ∀ i j k, F j i k = -F i j k)
      (h23 : ∀ i j k, F i k j = -F i j k),
      (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
        R.readout () () (tetraDefect F r i j k)) =
        4 * (Fintype.card V : ℝ) *
          (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2)) ∧
    (4 ≤ Fintype.card V → ∀ C : ℝ,
      (∀ (F : V → V → V → ℝ)
        (h12 : ∀ i j k, F j i k = -F i j k)
        (h23 : ∀ i j k, F i k j = -F i j k),
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (tetraDefect F r i j k) ^ 2) ≤
          C * (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2)) →
      4 * (Fintype.card V : ℝ) ≤ C)

theorem actual_law : arena.{u}.Law actual := by
  intro V _ _
  constructor
  · intro F h12 h23
    have hs := @_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal V _ _
    simpa [actual, realize, signature] using
      hs.1 F h12 h23
  · intro hcard C H
    have hs := @_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal V _ _
    exact hs.2 hcard C H

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let F : V → V → V → ℝ := fun _ _ _ => 0
  have hbad := (h (V := V)).1 F (by intros; simp [F]) (by intros; simp [F])
  norm_num [rejected, realize, signature, F, tetraDefect, edgeCoboundary,
    averageEdge, contraction] at hbad

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, signature]

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal.{u}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "SimplexTwoCochainL2Projection") "tetra_defect_energy_eq_and_optimal") "Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection/Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.arena.{u}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.arena.{u}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.arena.) (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration.{u}).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"tetra_defect_energy_eq_and_optimal\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration.{u}).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.observation0.{u} : {V : Type u} →
  [Fintype.{u} V] →
    [Nonempty.{u + 1} V] →
      (F : V → V → V → Real) →
        (h12 : ∀ (i j k : V), @Eq.{1} Real (F j i k) (@Neg.neg.{0} Real Real.instNeg (F i j k))) →
          (h23 : ∀ (i j k : V), @Eq.{1} Real (F i k j) (@Neg.neg.{0} Real Real.instNeg (F i j k))) →
            (r i j k : V) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.signature PUnit.unit.{1}
                PUnit.unit.{1} :=
  fun {V : Type u} [Fintype.{u} V] [Nonempty.{u + 1} V] (F : V → V → V → Real)
    (h12 : ∀ (i j k : V), @Eq.{1} Real (F j i k) (@Neg.neg.{0} Real Real.instNeg (F i j k)))
    (h23 : ∀ (i j k : V), @Eq.{1} Real (F i k j) (@Neg.neg.{0} Real Real.instNeg (F i j k))) (r i j k : V) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.signature
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.actual PUnit.unit.{1} PUnit.unit.{1}
    (@D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetraDefect.{u} V F r i j k)

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"tetra_defect_energy_eq_and_optimal\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal, part := .type, path := [.body, .body, .body, .function, .argument, .body, .body, .body, .function, .argument, .argument, .body, .argument, .body, .argument, .body, .argument, .body], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"tetra_defect_energy_eq_and_optimal\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration.{u}).actual (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration.{u}).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration.{u}).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainL2Projection\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
