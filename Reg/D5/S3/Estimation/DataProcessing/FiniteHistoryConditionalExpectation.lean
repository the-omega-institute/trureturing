import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.FiniteHistoryFamily

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

/-- The statement parameter is checked against the imported ConstantInfo.type.
The bridge is definitional on the complete thirteen-binder law. -/
def registration : Registration arena.{u,v} (FullLaw identityFamily) where
  actual := actual
  bridge := Iff.rfl
  variation := Reg.Support.FiniteHistoryFamily.variation
  sensitivity := Reg.Support.FiniteHistoryFamily.sensitivity
  dependence := Reg.Support.FiniteHistoryFamily.dependence

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} signature.{u_1, u_2} (fun _ _ w => w.2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DataProcessing") "FiniteHistoryConditionalExpectation") "history_law_conditional_expectation") "Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation/D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} signature.{u_1, u_2} (fun _ _ w => w.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, definition := none, coordinates := #[0, 1, 11], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"], stateBinder := 16, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.observationFact0, `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.anchorEnumeration }


end Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation


noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} (D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.arena.) (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"history_law_conditional_expectation\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.observation0.{u_1, u_2} : {J : Type u_1} →
  {Z : Nat → Type u_2} →
    [inst : Fintype.{u_1} J] →
      [inst_1 : (n : Nat) → Fintype.{u_2} (Z n)] →
        [inst_2 : MeasurableSpace.{u_1} J] →
          [@MeasurableSingletonClass.{u_1} J inst_2] →
            [inst_4 : (n : Nat) → MeasurableSpace.{u_2} (Z n)] →
              [∀ (n : Nat), @MeasurableSingletonClass.{u_2} (Z n) (inst_4 n)] →
                (ν : J → Real) →
                  (hν :
                      And
                        (∀ (j : J),
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (ν j))
                        (@Eq.{1} Real
                          (@Finset.sum.{u_1, 0} J Real Real.instAddCommMonoid (@Finset.univ.{u_1} J inst) fun (j : J) =>
                            ν j)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                    (K :
                        (n : Nat) →
                          J →
                            D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z n →
                              Z n → Real) →
                      (N : Nat) →
                        (hK :
                            ∀ (n : Nat),
                              @LT.lt.{0} Nat instLTNat n N →
                                And
                                  (∀ (j : J)
                                    (h :
                                      D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2}
                                        Z n)
                                    (z : Z n),
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (K n j h z))
                                  (∀ (j : J)
                                    (h :
                                      D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2}
                                        Z n),
                                    @Eq.{1} Real
                                      (@Finset.sum.{u_2, 0} (Z n) Real Real.instAddCommMonoid
                                        (@Finset.univ.{u_2} (Z n) (inst_1 n)) fun (z : Z n) => K n j h z)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                          (t : Nat) →
                            (ht : @LE.le.{0} Nat instLENat t N) →
                              (f :
                                  J →
                                    D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z
                                        t →
                                      Real) →
                                (ω :
                                    Prod.{u_1, u_2} J
                                      (D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2}
                                        Z N)) →
                                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max
                                        (u_1 + 1) (u_2 + 1),
                                      max u_1 u_2, 0, u_2, 0}
                                    D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.signature.{u_1, u_2}
                                    PUnit.unit.{1}
                                    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1)
                                      (fun (J : Type u_1) =>
                                        @Sigma.{u_2 + 1, 0} (Nat → Type u_2) fun (Z : Nat → Type u_2) => Nat)
                                      J (@Sigma.mk.{u_2 + 1, 0} (Nat → Type u_2) (fun (Z : Nat → Type u_2) => Nat) Z N)) :=
  fun {J : Type u_1} {Z : Nat → Type u_2} [Fintype.{u_1} J] [(n : Nat) → Fintype.{u_2} (Z n)] [MeasurableSpace.{u_1} J]
    [@MeasurableSingletonClass.{u_1} J inst_2] [(n : Nat) → MeasurableSpace.{u_2} (Z n)]
    [∀ (n : Nat), @MeasurableSingletonClass.{u_2} (Z n) (inst_4 n)] (ν : J → Real)
    (hν :
      And
        (∀ (j : J),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (ν j))
        (@Eq.{1} Real
          (@Finset.sum.{u_1, 0} J Real Real.instAddCommMonoid (@Finset.univ.{u_1} J inst) fun (j : J) => ν j)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (K :
      (n : Nat) →
        J → D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z n → Z n → Real)
    (N : Nat)
    (hK :
      ∀ (n : Nat),
        @LT.lt.{0} Nat instLTNat n N →
          And
            (∀ (j : J) (h : D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z n)
              (z : Z n),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (K n j h z))
            (∀ (j : J) (h : D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z n),
              @Eq.{1} Real
                (@Finset.sum.{u_2, 0} (Z n) Real Real.instAddCommMonoid (@Finset.univ.{u_2} (Z n) (inst_1 n))
                  fun (z : Z n) => K n j h z)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (t : Nat) (ht : @LE.le.{0} Nat instLENat t N)
    (f : J → D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z t → Real)
    (ω : Prod.{u_1, u_2} J (D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.History.{u_2} Z N)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
        u_2, 0}
    D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.signature.{u_1, u_2}
    D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.actual.{u_1, u_2} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1)
      (fun (J : Type u_1) => @Sigma.{u_2 + 1, 0} (Nat → Type u_2) fun (Z : Nat → Type u_2) => Nat) J
      (@Sigma.mk.{u_2 + 1, 0} (Nat → Type u_2) (fun (Z : Nat → Type u_2) => Nat) Z N))
    ω

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"history_law_conditional_expectation\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .body, .body, .body, .function, .argument, .argument, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"history_law_conditional_expectation\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.{u_1, u_2}).actual (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DataProcessing\",\"FiniteHistoryConditionalExpectation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, declaration := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
