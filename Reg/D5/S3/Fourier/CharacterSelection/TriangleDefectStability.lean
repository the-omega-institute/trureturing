import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.TriangleDefectStability
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability

universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 3 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} {A : Type v} [Fintype V] [Nonempty V] [AddCommGroup A]
    (a : V → V → A)
    (hdiag : ∀ i, a i i = 0)
    (hskew : ∀ i j, a j i = -a i j),
    (∑ r : V, edgeDefects a r) = triangleDefects a ∧
      (∃ r : V, Fintype.card V * edgeDefects a r ≤ triangleDefects a) ∧
      ∀ p : V → A,
        triangleDefects a ≤
          R.readout () () (Fintype.card V - 2) * potentialErrors a p

theorem actual_law : arena.{u, v}.Law actual := by
  intro V A _ _ _ a hdiag hskew
  simpa [actual, realize, signature] using
    (_root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound
      a hdiag hskew)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 3)
  let A := ULift.{v} (ZMod 2)
  let a : V → V → A := fun i j =>
    if i = j then ULift.up (0 : ZMod 2) else ULift.up (1 : ZMod 2)
  have hdiag : ∀ i, a i i = 0 := by
    intro i; apply ULift.ext; simp [a]
  have hskew : ∀ i j, a j i = -a i j := by
    intro i j
    by_cases hij : i = j
    · subst j; apply ULift.ext; simp only [a]
      change (0 : ZMod 2) = -(0 : ZMod 2)
      norm_num
    · have hji : j ≠ i := by exact Ne.symm hij
      apply ULift.ext; simp only [a, hij, hji]
      change (1 : ZMod 2) = -(1 : ZMod 2)
      decide
  have hbad := (h (V := V) (A := A) a hdiag hskew).2.2 (fun _ => 0)
  norm_num [rejected, realize, signature, triangleDefects, a] at hbad
  have hterm := hbad (⟨0⟩ : V) (⟨1⟩ : V) (⟨2⟩ : V)
  have h01 : (⟨0⟩ : V) ≠ ⟨1⟩ := by decide
  have h12 : (⟨1⟩ : V) ≠ ⟨2⟩ := by decide
  have h20 : (⟨2⟩ : V) ≠ ⟨0⟩ := by decide
  simp only [if_neg h01, if_neg h12, if_neg h20] at hterm
  have hdown := congrArg ULift.down hterm
  change (1 : ZMod 2) + 1 + 1 = 0 at hdown
  exact (by decide : (1 : ZMod 2) + 1 + 1 ≠ 0) hdown

theorem sensitivity_proof : Sensitivity arena.{u, v} actual := by
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

def registration : Registration arena.{u, v} (arena.{u, v}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    _root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound.{u, v}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 3 * n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "TriangleDefectStability") "triangle_defects_incidence_repair_and_error_bound") "Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability/Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v})⟩,
  objectArena := .source ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 3 * n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.arena.{u, v}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.arena.{u, v}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.arena.) (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration.{u, v}).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"triangle_defects_incidence_repair_and_error_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration.{u, v}).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.observation0.{u, v} : {V : Type u} →
  {A : Type v} →
    [Fintype.{u} V] →
      [Nonempty.{u + 1} V] →
        [inst : AddCommGroup.{v} A] →
          (a : V → V → A) →
            (hdiag :
                ∀ (i : V),
                  @Eq.{v + 1} A (a i i)
                    (@OfNat.ofNat.{v} A (nat_lit 0)
                      (@Zero.toOfNat0.{v} A
                        (@NegZeroClass.toZero.{v} A
                          (@SubNegZeroMonoid.toNegZeroClass.{v} A
                            (@SubtractionMonoid.toSubNegZeroMonoid.{v} A
                              (@SubtractionCommMonoid.toSubtractionMonoid.{v} A
                                (@AddCommGroup.toDivisionAddCommMonoid.{v} A inst)))))))) →
              (hskew :
                  ∀ (i j : V),
                    @Eq.{v + 1} A (a j i)
                      (@Neg.neg.{v} A
                        (@NegZeroClass.toNeg.{v} A
                          (@SubNegZeroMonoid.toNegZeroClass.{v} A
                            (@SubtractionMonoid.toSubNegZeroMonoid.{v} A
                              (@SubtractionCommMonoid.toSubtractionMonoid.{v} A
                                (@AddCommGroup.toDivisionAddCommMonoid.{v} A inst)))))
                        (a i j))) →
                (p : V → A) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {V : Type u} {A : Type v} [inst : Fintype.{u} V] [Nonempty.{u + 1} V] [AddCommGroup.{v} A] (a : V → V → A)
    (hdiag :
      ∀ (i : V),
        @Eq.{v + 1} A (a i i)
          (@OfNat.ofNat.{v} A (nat_lit 0)
            (@Zero.toOfNat0.{v} A
              (@NegZeroClass.toZero.{v} A
                (@SubNegZeroMonoid.toNegZeroClass.{v} A
                  (@SubtractionMonoid.toSubNegZeroMonoid.{v} A
                    (@SubtractionCommMonoid.toSubtractionMonoid.{v} A
                      (@AddCommGroup.toDivisionAddCommMonoid.{v} A inst_2))))))))
    (hskew :
      ∀ (i j : V),
        @Eq.{v + 1} A (a j i)
          (@Neg.neg.{v} A
            (@NegZeroClass.toNeg.{v} A
              (@SubNegZeroMonoid.toNegZeroClass.{v} A
                (@SubtractionMonoid.toSubNegZeroMonoid.{v} A
                  (@SubtractionCommMonoid.toSubtractionMonoid.{v} A
                    (@AddCommGroup.toDivisionAddCommMonoid.{v} A inst_2)))))
            (a i j)))
    (p : V → A) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.signature
    Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.actual PUnit.unit.{1} PUnit.unit.{1}
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{u} V inst)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"triangle_defects_incidence_repair_and_error_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .body, .argument, .function, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"triangle_defects_incidence_repair_and_error_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `D5.S3.Fourier.CharacterSelection.TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration.{u, v}).actual (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration.{u, v}).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration.{u, v}).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"TriangleDefectStability\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability, declaration := `Reg.D5.S3.Fourier.CharacterSelection.TriangleDefectStability.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))
