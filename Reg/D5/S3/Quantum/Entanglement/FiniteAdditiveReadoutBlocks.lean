import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open scoped Classical

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

abbrev coefficientSignature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ x => (Real.sqrt x : ℂ)⁻¹) (fun e => nomatch e)

def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

def coefficientArena : Arena where
  signature := coefficientSignature
  Law observation := ∀ {G A B : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
    [Fintype G] [Fintype A] [Fintype B] [DecidableEq G] [DecidableEq A] [DecidableEq B]
    (alpha : G →+ A) (beta : G →+ B)
    (_hpair : Function.Injective (fun x : G => (alpha x, beta x))) (a : A) (b : B),
    actualCoefficient alpha beta a b = observation.readout () () (Fintype.card G : ℝ) *
      ∑ q : BlockQuotient alpha beta,
        if leftBlock alpha beta q a ∧ rightBlock alpha beta q b then (1 : ℂ) else 0

theorem coefficientActualLaw : coefficientArena.Law coefficientActual := by
  intro G A B _ _ _ _ _ _ _ _ _ alpha beta hpair a b
  exact actual_coefficient_block alpha beta hpair a b

theorem coefficientRejectedLaw : ¬ coefficientArena.Law coefficientRejected := by
  intro h
  have hbad := h (G := PUnit) (A := PUnit) (B := PUnit) 0 0
    (by intro x y _; exact Subsingleton.elim x y) PUnit.unit PUnit.unit
  norm_num [coefficientRejected, realize, actualCoefficient] at hbad

theorem coefficientDependence : ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  cases i
  refine ⟨(), 1, 4, ?_⟩
  norm_num [coefficientActual, realize]

def coefficientRegistration : Registration coefficientArena
    (coefficientArena.Law coefficientActual) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨coefficientActualLaw, coefficientRejected, coefficientRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected, ?_, rfl, coefficientRejectedLaw⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := coefficientDependence

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_coefficient_block.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} coefficientSignature
    (fun _ _ x => (Real.sqrt x : ℂ)⁻¹) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteAdditiveReadoutBlocks") "actual_coefficient_block") "Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks/Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(coefficientArena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(coefficientArena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (coefficientArena.{u_1, u_2, u_3}) ⟨(coefficientRegistration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} coefficientSignature
    (fun _ _ x => (Real.sqrt x : ℂ)⁻¹) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_coefficient_block, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.anchorEnumeration }


#print axioms coefficientActualLaw
#print axioms coefficientRejectedLaw
#print axioms coefficientRegistration

end Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
      Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientActual)
    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"actual_coefficient_block\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_coefficient_block, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientArena.{u_1, u_2, u_3}
    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientActual)
  Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.observation0.{u_1, u_2, u_3} : {G : Type u_1} →
  {A : Type u_2} →
    {B : Type u_3} →
      [inst : AddCommGroup.{u_1} G] →
        [inst_1 : AddCommGroup.{u_2} A] →
          [inst_2 : AddCommGroup.{u_3} B] →
            [Fintype.{u_1} G] →
              [Fintype.{u_2} A] →
                [Fintype.{u_3} B] →
                  [DecidableEq.{u_1 + 1} G] →
                    [DecidableEq.{u_2 + 1} A] →
                      [DecidableEq.{u_3 + 1} B] →
                        (alpha :
                            @AddMonoidHom.{u_1, u_2} G A
                              (@AddZeroClass.toAddZero.{u_1} G
                                (@AddMonoid.toAddZeroClass.{u_1} G
                                  (@SubNegMonoid.toAddMonoid.{u_1} G
                                    (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                              (@AddZeroClass.toAddZero.{u_2} A
                                (@AddMonoid.toAddZeroClass.{u_2} A
                                  (@SubNegMonoid.toAddMonoid.{u_2} A
                                    (@AddGroup.toSubNegMonoid.{u_2} A (@AddCommGroup.toAddGroup.{u_2} A inst_1)))))) →
                          (beta :
                              @AddMonoidHom.{u_1, u_3} G B
                                (@AddZeroClass.toAddZero.{u_1} G
                                  (@AddMonoid.toAddZeroClass.{u_1} G
                                    (@SubNegMonoid.toAddMonoid.{u_1} G
                                      (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                                (@AddZeroClass.toAddZero.{u_3} B
                                  (@AddMonoid.toAddZeroClass.{u_3} B
                                    (@SubNegMonoid.toAddMonoid.{u_3} B
                                      (@AddGroup.toSubNegMonoid.{u_3} B (@AddCommGroup.toAddGroup.{u_3} B inst_2)))))) →
                            (hpair :
                                @Function.Injective.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} G (Prod.{u_2, u_3} A B)
                                  fun (x : G) =>
                                  @Prod.mk.{u_2, u_3} A B
                                    (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                                      (@AddMonoidHom.{u_1, u_2} G A
                                        (@AddZeroClass.toAddZero.{u_1} G
                                          (@AddMonoid.toAddZeroClass.{u_1} G
                                            (@SubNegMonoid.toAddMonoid.{u_1} G
                                              (@AddGroup.toSubNegMonoid.{u_1} G
                                                (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                                        (@AddZeroClass.toAddZero.{u_2} A
                                          (@AddMonoid.toAddZeroClass.{u_2} A
                                            (@SubNegMonoid.toAddMonoid.{u_2} A
                                              (@AddGroup.toSubNegMonoid.{u_2} A
                                                (@AddCommGroup.toAddGroup.{u_2} A inst_1))))))
                                      G (fun (x : G) => A)
                                      (@AddMonoidHom.instFunLike.{u_1, u_2} G A
                                        (@AddZeroClass.toAddZero.{u_1} G
                                          (@AddMonoid.toAddZeroClass.{u_1} G
                                            (@SubNegMonoid.toAddMonoid.{u_1} G
                                              (@AddGroup.toSubNegMonoid.{u_1} G
                                                (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                                        (@AddZeroClass.toAddZero.{u_2} A
                                          (@AddMonoid.toAddZeroClass.{u_2} A
                                            (@SubNegMonoid.toAddMonoid.{u_2} A
                                              (@AddGroup.toSubNegMonoid.{u_2} A
                                                (@AddCommGroup.toAddGroup.{u_2} A inst_1))))))
                                      alpha x)
                                    (@DFunLike.coe.{max (u_1 + 1) (u_3 + 1), u_1 + 1, u_3 + 1}
                                      (@AddMonoidHom.{u_1, u_3} G B
                                        (@AddZeroClass.toAddZero.{u_1} G
                                          (@AddMonoid.toAddZeroClass.{u_1} G
                                            (@SubNegMonoid.toAddMonoid.{u_1} G
                                              (@AddGroup.toSubNegMonoid.{u_1} G
                                                (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                                        (@AddZeroClass.toAddZero.{u_3} B
                                          (@AddMonoid.toAddZeroClass.{u_3} B
                                            (@SubNegMonoid.toAddMonoid.{u_3} B
                                              (@AddGroup.toSubNegMonoid.{u_3} B
                                                (@AddCommGroup.toAddGroup.{u_3} B inst_2))))))
                                      G (fun (x : G) => B)
                                      (@AddMonoidHom.instFunLike.{u_1, u_3} G B
                                        (@AddZeroClass.toAddZero.{u_1} G
                                          (@AddMonoid.toAddZeroClass.{u_1} G
                                            (@SubNegMonoid.toAddMonoid.{u_1} G
                                              (@AddGroup.toSubNegMonoid.{u_1} G
                                                (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                                        (@AddZeroClass.toAddZero.{u_3} B
                                          (@AddMonoid.toAddZeroClass.{u_3} B
                                            (@SubNegMonoid.toAddMonoid.{u_3} B
                                              (@AddGroup.toSubNegMonoid.{u_3} B
                                                (@AddCommGroup.toAddGroup.{u_3} B inst_2))))))
                                      beta x)) →
                              (a : A) →
                                (b : B) →
                                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0,
                                      0}
                                    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientSignature
                                    PUnit.unit.{1} PUnit.unit.{1} :=
  fun {G : Type u_1} {A : Type u_2} {B : Type u_3} [AddCommGroup.{u_1} G] [AddCommGroup.{u_2} A] [AddCommGroup.{u_3} B]
    [inst_3 : Fintype.{u_1} G] [Fintype.{u_2} A] [Fintype.{u_3} B] [DecidableEq.{u_1 + 1} G] [DecidableEq.{u_2 + 1} A]
    [DecidableEq.{u_3 + 1} B]
    (alpha :
      @AddMonoidHom.{u_1, u_2} G A
        (@AddZeroClass.toAddZero.{u_1} G
          (@AddMonoid.toAddZeroClass.{u_1} G
            (@SubNegMonoid.toAddMonoid.{u_1} G
              (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
        (@AddZeroClass.toAddZero.{u_2} A
          (@AddMonoid.toAddZeroClass.{u_2} A
            (@SubNegMonoid.toAddMonoid.{u_2} A
              (@AddGroup.toSubNegMonoid.{u_2} A (@AddCommGroup.toAddGroup.{u_2} A inst_1))))))
    (beta :
      @AddMonoidHom.{u_1, u_3} G B
        (@AddZeroClass.toAddZero.{u_1} G
          (@AddMonoid.toAddZeroClass.{u_1} G
            (@SubNegMonoid.toAddMonoid.{u_1} G
              (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
        (@AddZeroClass.toAddZero.{u_3} B
          (@AddMonoid.toAddZeroClass.{u_3} B
            (@SubNegMonoid.toAddMonoid.{u_3} B
              (@AddGroup.toSubNegMonoid.{u_3} B (@AddCommGroup.toAddGroup.{u_3} B inst_2))))))
    (hpair :
      @Function.Injective.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} G (Prod.{u_2, u_3} A B) fun (x : G) =>
        @Prod.mk.{u_2, u_3} A B
          (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
            (@AddMonoidHom.{u_1, u_2} G A
              (@AddZeroClass.toAddZero.{u_1} G
                (@AddMonoid.toAddZeroClass.{u_1} G
                  (@SubNegMonoid.toAddMonoid.{u_1} G
                    (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
              (@AddZeroClass.toAddZero.{u_2} A
                (@AddMonoid.toAddZeroClass.{u_2} A
                  (@SubNegMonoid.toAddMonoid.{u_2} A
                    (@AddGroup.toSubNegMonoid.{u_2} A (@AddCommGroup.toAddGroup.{u_2} A inst_1))))))
            G (fun (x : G) => A)
            (@AddMonoidHom.instFunLike.{u_1, u_2} G A
              (@AddZeroClass.toAddZero.{u_1} G
                (@AddMonoid.toAddZeroClass.{u_1} G
                  (@SubNegMonoid.toAddMonoid.{u_1} G
                    (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
              (@AddZeroClass.toAddZero.{u_2} A
                (@AddMonoid.toAddZeroClass.{u_2} A
                  (@SubNegMonoid.toAddMonoid.{u_2} A
                    (@AddGroup.toSubNegMonoid.{u_2} A (@AddCommGroup.toAddGroup.{u_2} A inst_1))))))
            alpha x)
          (@DFunLike.coe.{max (u_1 + 1) (u_3 + 1), u_1 + 1, u_3 + 1}
            (@AddMonoidHom.{u_1, u_3} G B
              (@AddZeroClass.toAddZero.{u_1} G
                (@AddMonoid.toAddZeroClass.{u_1} G
                  (@SubNegMonoid.toAddMonoid.{u_1} G
                    (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
              (@AddZeroClass.toAddZero.{u_3} B
                (@AddMonoid.toAddZeroClass.{u_3} B
                  (@SubNegMonoid.toAddMonoid.{u_3} B
                    (@AddGroup.toSubNegMonoid.{u_3} B (@AddCommGroup.toAddGroup.{u_3} B inst_2))))))
            G (fun (x : G) => B)
            (@AddMonoidHom.instFunLike.{u_1, u_3} G B
              (@AddZeroClass.toAddZero.{u_1} G
                (@AddMonoid.toAddZeroClass.{u_1} G
                  (@SubNegMonoid.toAddMonoid.{u_1} G
                    (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
              (@AddZeroClass.toAddZero.{u_3} B
                (@AddMonoid.toAddZeroClass.{u_3} B
                  (@SubNegMonoid.toAddMonoid.{u_3} B
                    (@AddGroup.toSubNegMonoid.{u_3} B (@AddCommGroup.toAddGroup.{u_3} B inst_2))))))
            beta x))
    (a : A) (b : B) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientSignature
    Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientActual PUnit.unit.{1} PUnit.unit.{1}
    (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} G inst_3))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"actual_coefficient_block\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_coefficient_block, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"actual_coefficient_block\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_coefficient_block, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteAdditiveReadoutBlocks\",\"coefficientRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.coefficientRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
