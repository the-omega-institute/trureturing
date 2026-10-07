import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Module (finrank)
open scoped BigOperators InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v),
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ kyFanSum (R.readout ⟨()⟩ () k) A

theorem actual_law : arena.{u}.Law actual := by
  intro 𝕜 E F _ _ _ _ _ _ _ A k hk u v hu hv
  exact re_sum_inner_map_le_ky_fan_sum hk hu hv

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℝ (ULift.{u} (Fin 1))
  let v : Fin 1 → E := fun i => EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℝ ⟨i⟩
  have hv : Orthonormal ℝ v := by
    exact (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℝ).orthonormal.comp
      (fun i : Fin 1 => ULift.up i) ULift.up_injective
  have hk : 1 ≤ finrank ℝ E := by simp [E]
  have hb := h (A := LinearMap.id (R := ℝ) (M := E)) hk hv hv
  have hinner : ∀ i : Fin 1, inner ℝ (v i) (v i) = 1 := by
    intro i
    exact (orthonormal_iff_ite.mp hv i i).trans (if_pos rfl)
  change (∑ i : Fin 1, inner ℝ (v i) (v i)) ≤ 0 at hb
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    one_smul] at hb
  exact (not_le_of_gt (by norm_num : (0 : ℝ) < 1)) hb

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.re_sum_inner_map_le_ky_fan_sum.{u}) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ k => k) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteSectorChannelOptimality") "re_sum_inner_map_le_ky_fan_sum") "Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational/Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ k => k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.re_sum_inner_map_le_ky_fan_sum, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.actual.{u})
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"re_sum_inner_map_le_ky_fan_sum\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.re_sum_inner_map_le_ky_fan_sum, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.actual.{u})
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.roleEnumeration.{u} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u, 0} Unit) where
  values := [@ULift.up.{u, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.observation0.{u} : {𝕜 : Type} →
  {E F : Type u} →
    [inst : RCLike.{0} 𝕜] →
      [inst_1 : NormedAddCommGroup.{u} E] →
        [inst_2 : @InnerProductSpace.{0, u} 𝕜 E inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)] →
          [@FiniteDimensional.{0, u} 𝕜 E
                (@Field.toDivisionRing.{0} 𝕜
                  (@NormedField.toField.{0} 𝕜
                    (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))
                (@NormedAddCommGroup.toAddCommGroup.{u} E inst_1)
                (@NormedSpace.toModule.{0, u} 𝕜 E
                  (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
                  (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 E inst
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1) inst_2))] →
            [inst_4 : NormedAddCommGroup.{u} F] →
              [inst_5 :
                  @InnerProductSpace.{0, u} 𝕜 F inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)] →
                [@FiniteDimensional.{0, u} 𝕜 F
                      (@Field.toDivisionRing.{0} 𝕜
                        (@NormedField.toField.{0} 𝕜
                          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))
                      (@NormedAddCommGroup.toAddCommGroup.{u} F inst_4)
                      (@NormedSpace.toModule.{0, u} 𝕜 F
                        (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)
                        (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 F inst
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4) inst_5))] →
                  {A :
                      @LinearMap.{0, 0, u, u} 𝕜 𝕜
                        (@DivisionSemiring.toSemiring.{0} 𝕜
                          (@Semifield.toDivisionSemiring.{0} 𝕜
                            (@Field.toSemifield.{0} 𝕜
                              (@NormedField.toField.{0} 𝕜
                                (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))
                        (@DivisionSemiring.toSemiring.{0} 𝕜
                          (@Semifield.toDivisionSemiring.{0} 𝕜
                            (@Field.toSemifield.{0} 𝕜
                              (@NormedField.toField.{0} 𝕜
                                (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))
                        (@RingHom.id.{0} 𝕜
                          (@Semiring.toNonAssocSemiring.{0} 𝕜
                            (@DivisionSemiring.toSemiring.{0} 𝕜
                              (@Semifield.toDivisionSemiring.{0} 𝕜
                                (@Field.toSemifield.{0} 𝕜
                                  (@NormedField.toField.{0} 𝕜
                                    (@DenselyNormedField.toNormedField.{0} 𝕜
                                      (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))))
                        E F (@AddCommGroup.toAddCommMonoid.{u} E (@NormedAddCommGroup.toAddCommGroup.{u} E inst_1))
                        (@AddCommGroup.toAddCommMonoid.{u} F (@NormedAddCommGroup.toAddCommGroup.{u} F inst_4))
                        (@NormedSpace.toModule.{0, u} 𝕜 E
                          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
                          (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 E inst
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1) inst_2))
                        (@NormedSpace.toModule.{0, u} 𝕜 F
                          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)
                          (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 F inst
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4) inst_5))} →
                    {k : Nat} →
                      (hk :
                          @LE.le.{0} Nat instLENat k
                            (@Module.finrank.{0, u} 𝕜 E
                              (@DivisionSemiring.toSemiring.{0} 𝕜
                                (@Semifield.toDivisionSemiring.{0} 𝕜
                                  (@Field.toSemifield.{0} 𝕜
                                    (@NormedField.toField.{0} 𝕜
                                      (@DenselyNormedField.toNormedField.{0} 𝕜
                                        (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))
                              (@AddCommGroup.toAddCommMonoid.{u} E (@NormedAddCommGroup.toAddCommGroup.{u} E inst_1))
                              (@NormedSpace.toModule.{0, u} 𝕜 E
                                (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
                                (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 E inst
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1) inst_2)))) →
                        {u : Fin k → F} →
                          {v : Fin k → E} →
                            (hu :
                                @Orthonormal.{0, u, 0} 𝕜 F inst
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4) inst_5 (Fin k) u) →
                              (hv :
                                  @Orthonormal.{0, u, 0} 𝕜 E inst
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1) inst_2 (Fin k) v) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u, 0, 0}
                                  Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.signature.{u}
                                  (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {𝕜 : Type} {E F : Type u} [RCLike.{0} 𝕜] [NormedAddCommGroup.{u} E]
    [@InnerProductSpace.{0, u} 𝕜 E inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)]
    [@FiniteDimensional.{0, u} 𝕜 E
        (@Field.toDivisionRing.{0} 𝕜
          (@NormedField.toField.{0} 𝕜
            (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))
        (@NormedAddCommGroup.toAddCommGroup.{u} E inst_1)
        (@NormedSpace.toModule.{0, u} 𝕜 E
          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
          (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 E inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
            inst_2))]
    [NormedAddCommGroup.{u} F]
    [@InnerProductSpace.{0, u} 𝕜 F inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)]
    [@FiniteDimensional.{0, u} 𝕜 F
        (@Field.toDivisionRing.{0} 𝕜
          (@NormedField.toField.{0} 𝕜
            (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))
        (@NormedAddCommGroup.toAddCommGroup.{u} F inst_4)
        (@NormedSpace.toModule.{0, u} 𝕜 F
          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)
          (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 F inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)
            inst_5))]
    {A :
      @LinearMap.{0, 0, u, u} 𝕜 𝕜
        (@DivisionSemiring.toSemiring.{0} 𝕜
          (@Semifield.toDivisionSemiring.{0} 𝕜
            (@Field.toSemifield.{0} 𝕜
              (@NormedField.toField.{0} 𝕜
                (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))
        (@DivisionSemiring.toSemiring.{0} 𝕜
          (@Semifield.toDivisionSemiring.{0} 𝕜
            (@Field.toSemifield.{0} 𝕜
              (@NormedField.toField.{0} 𝕜
                (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))
        (@RingHom.id.{0} 𝕜
          (@Semiring.toNonAssocSemiring.{0} 𝕜
            (@DivisionSemiring.toSemiring.{0} 𝕜
              (@Semifield.toDivisionSemiring.{0} 𝕜
                (@Field.toSemifield.{0} 𝕜
                  (@NormedField.toField.{0} 𝕜
                    (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))))
        E F (@AddCommGroup.toAddCommMonoid.{u} E (@NormedAddCommGroup.toAddCommGroup.{u} E inst_1))
        (@AddCommGroup.toAddCommMonoid.{u} F (@NormedAddCommGroup.toAddCommGroup.{u} F inst_4))
        (@NormedSpace.toModule.{0, u} 𝕜 E
          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
          (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 E inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
            inst_2))
        (@NormedSpace.toModule.{0, u} 𝕜 F
          (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)
          (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 F inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4)
            inst_5))}
    {k : Nat}
    (hk :
      @LE.le.{0} Nat instLENat k
        (@Module.finrank.{0, u} 𝕜 E
          (@DivisionSemiring.toSemiring.{0} 𝕜
            (@Semifield.toDivisionSemiring.{0} 𝕜
              (@Field.toSemifield.{0} 𝕜
                (@NormedField.toField.{0} 𝕜
                  (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))))))
          (@AddCommGroup.toAddCommMonoid.{u} E (@NormedAddCommGroup.toAddCommGroup.{u} E inst_1))
          (@NormedSpace.toModule.{0, u} 𝕜 E
            (@DenselyNormedField.toNormedField.{0} 𝕜 (@RCLike.toDenselyNormedField.{0} 𝕜 inst))
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1)
            (@InnerProductSpace.toNormedSpace.{0, u} 𝕜 E inst
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1) inst_2))))
    {u : Fin k → F} {v : Fin k → E}
    (hu : @Orthonormal.{0, u, 0} 𝕜 F inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} F inst_4) inst_5 (Fin k) u)
    (hv :
      @Orthonormal.{0, u, 0} 𝕜 E inst (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} E inst_1) inst_2 (Fin k) v) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.signature.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.actual.{u} (@ULift.up.{u, 0} Unit Unit.unit)
    PUnit.unit.{1} k

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"re_sum_inner_map_le_ky_fan_sum\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.re_sum_inner_map_le_ky_fan_sum, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"re_sum_inner_map_le_ky_fan_sum\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.re_sum_inner_map_le_ky_fan_sum, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration.{u}).actual (Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration.{u}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration.{u}).variation.1 (Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorRectangularVariational\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
