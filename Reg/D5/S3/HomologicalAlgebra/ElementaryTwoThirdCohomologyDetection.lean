import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
import Reg.Support.DependentFamily
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

open CategoryTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
namespace Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
noncomputable section
open Classical

structure Parameters where
  M : Type
  group : AddCommGroup M
  rank : ℕ

abbrev cohomology (p : Parameters) := by
  letI := p.group
  exact groupCohomology (Rep.trivial ℤ (Multiplicative (Fin p.rank → ZMod 2)) p.M) 3

abbrev signature : Signature where
  Params := Parameters
  State := fun p => (cohomology p : Type)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ c => c = 0) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Type) [AddCommGroup M] (half : ∀ m : M, ∃ k, k+k=m)
    (r : ℕ) (c : groupCohomology (Rep.trivial ℤ (Multiplicative (Fin r → ZMod 2)) M) 3),
    (∀ g : Multiplicative (Fin r → ZMod 2), g ≠ 1 →
      groupCohomology.map (Subgroup.zpowers g).subtype (𝟙 _) 3 c = 0) →
    R.readout () ⟨M, inferInstance, r⟩ c

theorem actual_law : arena.Law actual := by
  intro M _ half r c hr
  exact cyclic_restriction_detects_third_cohomology M half r c hr

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ℚ (fun m => ⟨m/2, by ring⟩) 0 0 (by intro g hg; exact (hg (Subsingleton.elim _ _)).elim)


theorem nonzero_sample : ∃ c : groupCohomology
    (Rep.trivial ℤ (Multiplicative (Fin 1 → ZMod 2)) (ZMod 2)) 3, c ≠ 0 := by
  let G := Multiplicative (Fin 1 → ZMod 2)
  let g : G := Multiplicative.ofAdd (fun _ => 1)
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := by
    intro x
    have hx : x=1 ∨ x=g := by
      generalize he : x.toAdd 0 = z
      fin_cases z
      · left; apply Multiplicative.ofAdd.injective; ext i; fin_cases i; exact he
      · right; apply Multiplicative.ofAdd.injective; ext i; fin_cases i; exact he
    rcases hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers g
  let A := Rep.trivial ℤ G (ZMod 2)
  have hn : A.norm.hom (1 : ZMod 2) = 0 := by
    simp [A, G, Rep.norm, Representation.norm, Rep.trivial, Representation.trivial,
      Fintype.card_fun, ZMod.card]
    decide
  let z : LinearMap.ker A.norm.hom.toLinearMap := ⟨1, hn⟩
  refine ⟨Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 3 (by decide) z, ?_⟩
  intro hz
  have hmem := (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff A g hg 3 (by decide) z).mp hz
  obtain ⟨m,hm⟩ := hmem
  change (Rep.applyAsHom A g - 𝟙 A).hom m = (1 : ZMod 2) at hm
  have h0 : (Rep.applyAsHom A g - 𝟙 A).hom m = 0 := by
    change m - m = 0
    exact sub_self m
  rw [h0] at hm
  exact zero_ne_one hm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    obtain ⟨c,hc⟩ := nonzero_sample
    refine ⟨⟨ZMod 2, inferInstance, 1⟩, 0, c, ?_⟩
    change (0 = (0 : groupCohomology
      (Rep.trivial ℤ (Multiplicative (Fin 1 → ZMod 2)) (ZMod 2)) 3)) ≠ (c = 0)
    intro he
    exact hc (he ▸ rfl)

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
  coordinates := #[0, 3, 4]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body"], stateBinder := 4 }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ _ c => c = 0) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "HomologicalAlgebra") "ElementaryTwoThirdCohomologyDetection") "cyclic_restriction_detects_third_cohomology") "Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection/Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ _ c => c = 0) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, definition := none, coordinates := #[0, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalArenaFact, `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.sourceBridgeFact, `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.anchorEnumeration }

#print axioms registration
end
end Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection


noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
  Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{1, 0, 0, 0, 0}
    Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
      Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
      Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.actual)
    Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration)

noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"cyclic_restriction_detects_third_cohomology\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{1, 0, 0, 0, 0}
  Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
    Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.arena
    Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.actual)
  Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration)

noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"cyclic_restriction_detects_third_cohomology\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration).actual (Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration).variation.2.choose (Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration).variation.1 (Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"ElementaryTwoThirdCohomologyDetection\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection, declaration := `Reg.D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
