import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit ContinuousLinearMap MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
universe u v
namespace Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
structure Parameters where
  V : Type u
  W : Type v
  [normedV : NormedAddCommGroup V]
  [innerV : InnerProductSpace ℝ V]
  [finiteV : FiniteDimensional ℝ V]
  [normedW : NormedAddCommGroup W]
  [innerW : InnerProductSpace ℝ W]
  [completeW : CompleteSpace W]
  B : V →L[ℝ] V
  C : V →L[ℝ] W
  beta : ℝ
  eta : ℝ
attribute [instance] Parameters.normedV Parameters.innerV Parameters.finiteV
  Parameters.normedW Parameters.innerW Parameters.completeW
abbrev signature : Signature where
  Params := Parameters.{u,v}
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : ∀ (_ : Empty) p, signature.{u,v}.State p := fun e => nomatch e

def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ x => |x|) emptyAnchor

def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) emptyAnchor

def theoremLaw (family : Realization signature.{u,v}) : Prop := ∀
    {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (β η : ℝ) (_hβ : 0 < β) (_hη : 0 < η),
    let H := C.adjoint.comp C
    let G : ℝ → V →L[ℝ] V := fun T =>
      ∫ t in (0 : ℝ)..T, (C.comp (NormedSpace.exp (t • B))).adjoint.comp
        (C.comp (NormedSpace.exp (t • B)))
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ T : ℝ, 0 < T → T ≤ δ →
      family.readout () { V := V, W := W, B := B, C := C, beta := β, eta := η } ((1 / 2 : ℝ) * Real.log ((ContinuousLinearMap.id ℝ V +
          (β * η)⁻¹ • G T).det) -
        T / (2 * β * η) * LinearMap.trace ℝ V H.toLinearMap) ≤ K * T ^ 2

def arena : Arena where
  signature := signature.{u,v}
  Law := theoremLaw.{u,v}

theorem actual_law : arena.{u,v}.Law actual.{u,v} := by
  intro V W _ _ _ _ _ _ B C beta eta hbeta heta
  exact _root_.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information B C beta eta hbeta heta

theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  let V := EuclideanSpace ℝ (ULift.{u} (Fin 0))
  let W := EuclideanSpace ℝ (ULift.{v} (Fin 0))
  have hh := h (V:=V) (W:=W) 0 0 1 1 zero_lt_one zero_lt_one
  dsimp only [theoremLaw,rejected,realize] at hh
  obtain ⟨K,delta,hK,hdelta,hbound⟩ := hh
  let T := min (delta/2) (min 1 (2*(K+1))⁻¹)
  have hp:0<2*(K+1) := by linarith
  have hT:0<T := lt_min (half_pos hdelta) (lt_min zero_lt_one (inv_pos.mpr hp))
  have hTd:T≤delta := (min_le_left _ _).trans (by linarith)
  have hT1:T≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hTi:T≤(2*(K+1))⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hb := hbound T hT hTd
  have hKi:K*(2*(K+1))⁻¹<1 := (mul_inv_lt_iff₀ hp).2 (by linarith)
  have hKT:K*T<1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hTi hK) hKi
  nlinarith [mul_nonneg hK (mul_nonneg hT.le (sub_nonneg.mpr hT1))]

theorem dependence_proof : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  let V := EuclideanSpace ℝ (ULift.{u} (Fin 0))
  let W := EuclideanSpace ℝ (ULift.{v} (Fin 0))
  refine ⟨{V:=V,W:=W,B:=0,C:=0,beta:=1,eta:=1},0,1,?_⟩
  norm_num [actual,realize]

def registration : Registration arena.{u,v} (arena.{u,v}.Law actual.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro other hne
      exact (hne (by cases role; cases other; rfl)).elim
    · intro e; exact nomatch e
  dependence := dependence_proof

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0} signature.{u_1, u_2} (fun _ _ x => |x|) emptyAnchor.{u_1, u_2})) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Linear") "PhysicalFixedNoiseInformation") "physical_fixed_noise_information") "Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation/Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0} signature.{u_1, u_2} (fun _ _ x => |x|) emptyAnchor.{u_1, u_2}),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, definition := none, coordinates := #[0, 1, 8, 9, 10, 11], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.observationFact0, `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.anchorEnumeration }

end Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation


noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0}
  Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0}
      Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
      Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.actual.{u_1, u_2})
    Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"physical_fixed_noise_information\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0}
  Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.arena.{u_1, u_2}
    Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.actual.{u_1, u_2})
  Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.observation0.{u_1, u_2} : {V : Type u_1} →
  {W : Type u_2} →
    [inst : NormedAddCommGroup.{u_1} V] →
      [inst_1 :
          @InnerProductSpace.{0, u_1} Real V Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)] →
        [inst_2 :
            @FiniteDimensional.{0, u_1} Real V Real.instDivisionRing (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)
              (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))] →
          [inst_3 : NormedAddCommGroup.{u_2} W] →
            [inst_4 :
                @InnerProductSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)] →
              [inst_5 :
                  @CompleteSpace.{u_2} W
                    (@PseudoMetricSpace.toUniformSpace.{u_2} W
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)))] →
                (B :
                    @ContinuousLinearMap.{0, 0, u_1, u_1} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) V
                      (@UniformSpace.toTopologicalSpace.{u_1} V
                        (@PseudoMetricSpace.toUniformSpace.{u_1} V
                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
                      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) V
                      (@UniformSpace.toTopologicalSpace.{u_1} V
                        (@PseudoMetricSpace.toUniformSpace.{u_1} V
                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
                      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                      (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                        (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
                      (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                        (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))) →
                  (C :
                      @ContinuousLinearMap.{0, 0, u_1, u_2} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) V
                        (@UniformSpace.toTopologicalSpace.{u_1} V
                          (@PseudoMetricSpace.toUniformSpace.{u_1} V
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
                        (@UniformSpace.toTopologicalSpace.{u_2} W
                          (@PseudoMetricSpace.toUniformSpace.{u_2} W
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                        (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                          (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
                        (@NormedSpace.toModule.{0, u_2} Real W Real.normedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                          (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))) →
                    (β η : Real) →
                      (hβ :
                          @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β) →
                        (hη :
                            @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) η) →
                          (K δ T : Real) →
                            @LT.lt.{0} Real Real.instLT
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T →
                              @LE.le.{0} Real Real.instLE T δ →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1)
                                      (u_2 + 1),
                                    0, 0, 0, 0}
                                  Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.signature.{u_1, u_2}
                                  PUnit.unit.{1}
                                  (@Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.Parameters.mk.{u_1, u_2} V W
                                    inst inst_1 inst_2 inst_3 inst_4 inst_5 B C β η) :=
  fun {V : _} {W : _} [inst : _] [inst_1 : _] [_] [inst_3 : _] [inst_4 : _] [_] (B : _) (C : _) (β η : _) (hβ : _)
    (hη : _) =>
  have H : _ :=
    @ContinuousLinearMap.comp.{0, 0, 0, u_1, u_2, u_1} Real Real Real Real.semiring
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real
          (@Field.toSemifield.{0} Real
            (@NormedField.toField.{0} Real
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real
          (@Field.toSemifield.{0} Real
            (@NormedField.toField.{0} Real
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
      (@RingHom.id.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
      (@RingHom.id.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
      V
      (@UniformSpace.toTopologicalSpace.{u_1} V
        (@PseudoMetricSpace.toUniformSpace.{u_1} V
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
      (@UniformSpace.toTopologicalSpace.{u_2} W
        (@PseudoMetricSpace.toUniformSpace.{u_2} W
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
      (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)) V
      (@UniformSpace.toTopologicalSpace.{u_1} V
        (@PseudoMetricSpace.toUniformSpace.{u_1} V
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
      (@NormedSpace.toModule.{0, u_1} Real V Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
        (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
      (@NormedSpace.toModule.{0, u_2} Real W
        (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
        (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
      (@NormedSpace.toModule.{0, u_1} Real V
        (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
        (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
      (@RingHomCompTriple.ids.{0, 0} Real Real Real.semiring
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real
            (@Field.toSemifield.{0} Real
              (@NormedField.toField.{0} Real
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
        (@RingHom.id.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))))
      (@DFunLike.coe.{(max u_2 u_1) + 1, (max u_2 u_1) + 1, (max u_2 u_1) + 1}
        (@LinearIsometryEquiv.{0, 0, max u_2 u_1, max u_2 u_1} Real Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
          (@starRingEnd.{0} Real
            (@Semifield.toCommSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
            (@RCLike.toStarRing.{0} Real Real.instRCLike))
          (@starRingEnd.{0} Real
            (@Semifield.toCommSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
            (@RCLike.toStarRing.{0} Real Real.instRCLike))
          (@RingHomInvPair.instStarRingEnd.{0} Real
            (@Semifield.toCommSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
            (@RCLike.toStarRing.{0} Real Real.instRCLike))
          (@RingHomInvPair.instStarRingEnd.{0} Real
            (@Semifield.toCommSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
            (@RCLike.toStarRing.{0} Real Real.instRCLike))
          (@ContinuousLinearMap.{0, 0, u_1, u_2} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))
          (@ContinuousLinearMap.{0, 0, u_2, u_1} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)) V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
          (@ContinuousLinearMap.toSeminormedAddCommGroup.{0, 0, u_1, u_2} Real Real V W
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
            (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)
            (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            (@RingHomIsometric.ids.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
          (@ContinuousLinearMap.toSeminormedAddCommGroup.{0, 0, u_2, u_1} Real Real W V
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
            (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)
            (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            (@RingHomIsometric.ids.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
          (@ContinuousLinearMap.module.{0, 0, 0, u_1, u_2} Real Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
            W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
            (@smulCommClass_self.{0, u_2} Real W
              (@CommRing.toCommMonoid.{0} Real
                (@Field.toCommRing.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@DistribMulAction.toMulAction.{0, u_2} Real W
                (@CommMonoid.toMonoid.{0} Real
                  (@CommRing.toCommMonoid.{0} Real
                    (@Field.toCommRing.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                (@AddCommMonoid.toAddMonoid.{u_2} W
                  (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                (@Module.toDistribMulAction.{0, u_2} Real W
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                  (@NormedSpace.toModule.{0, u_2} Real W
                    (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                    (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))))
            (@UniformContinuousConstSMul.instContinuousConstSMul.{0, u_2} Real W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)))
              (@SMulZeroClass.toSMul.{0, u_2} Real W
                (@AddZero.toZero.{u_2} W
                  (@AddZeroClass.toAddZero.{u_2} W
                    (@AddMonoid.toAddZeroClass.{u_2} W
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                (@DistribSMul.toSMulZeroClass.{0, u_2} Real W
                  (@AddMonoid.toAddZeroClass.{u_2} W
                    (@AddCommMonoid.toAddMonoid.{u_2} W
                      (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))
                  (@DistribMulAction.toDistribSMul.{0, u_2} Real W
                    (@Semiring.toMonoid.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                    (@AddCommMonoid.toAddMonoid.{u_2} W
                      (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                    (@Module.toDistribMulAction.{0, u_2} Real W
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                      (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                      (@NormedSpace.toModule.{0, u_2} Real W
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                        (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))))
              (@IsBoundedSMul.toUniformContinuousConstSMul.{0, u_2} Real W
                (@SeminormedRing.toPseudoMetricSpace.{0} Real
                  (@SeminormedCommRing.toSeminormedRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real
                      (@NormedField.toNormedCommRing.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))
                (@MulZeroClass.toZero.{0} Real
                  (@instMulZeroClassOfSemiring.{0} Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                (@NegZeroClass.toZero.{u_2} W
                  (@SubNegZeroMonoid.toNegZeroClass.{u_2} W
                    (@SubtractionMonoid.toSubNegZeroMonoid.{u_2} W
                      (@SubtractionCommMonoid.toSubtractionMonoid.{u_2} W
                        (@AddCommGroup.toDivisionAddCommMonoid.{u_2} W
                          (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                (@SMulZeroClass.toSMul.{0, u_2} Real W
                  (@AddZero.toZero.{u_2} W
                    (@AddZeroClass.toAddZero.{u_2} W
                      (@AddMonoid.toAddZeroClass.{u_2} W
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W
                            (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                  (@DistribSMul.toSMulZeroClass.{0, u_2} Real W
                    (@AddMonoid.toAddZeroClass.{u_2} W
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))
                    (@DistribMulAction.toDistribSMul.{0, u_2} Real W
                      (@Semiring.toMonoid.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                      (@Module.toDistribMulAction.{0, u_2} Real W
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                        (@NormedSpace.toModule.{0, u_2} Real W
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                          (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))))
                (@NormedSpace.toIsBoundedSMul.{0, u_2} Real W
                  (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                  (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            (@ContinuousLinearMap.addCommGroup._proof_7.{u_2} W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@SeminormedAddCommGroup.toAddCommGroup.{u_2} W
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))
              (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{u_2} W
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
          (@ContinuousLinearMap.module.{0, 0, 0, u_2, u_1} Real Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
            V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
            (@smulCommClass_self.{0, u_1} Real V
              (@CommRing.toCommMonoid.{0} Real
                (@Field.toCommRing.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@DistribMulAction.toMulAction.{0, u_1} Real V
                (@CommMonoid.toMonoid.{0} Real
                  (@CommRing.toCommMonoid.{0} Real
                    (@Field.toCommRing.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                (@AddCommMonoid.toAddMonoid.{u_1} V
                  (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                (@Module.toDistribMulAction.{0, u_1} Real V
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                  (@NormedSpace.toModule.{0, u_1} Real V
                    (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                    (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))))
            (@UniformContinuousConstSMul.instContinuousConstSMul.{0, u_1} Real V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
              (@SMulZeroClass.toSMul.{0, u_1} Real V
                (@AddZero.toZero.{u_1} V
                  (@AddZeroClass.toAddZero.{u_1} V
                    (@AddMonoid.toAddZeroClass.{u_1} V
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                (@DistribSMul.toSMulZeroClass.{0, u_1} Real V
                  (@AddMonoid.toAddZeroClass.{u_1} V
                    (@AddCommMonoid.toAddMonoid.{u_1} V
                      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))
                  (@DistribMulAction.toDistribSMul.{0, u_1} Real V
                    (@Semiring.toMonoid.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                    (@AddCommMonoid.toAddMonoid.{u_1} V
                      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                    (@Module.toDistribMulAction.{0, u_1} Real V
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                      (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                      (@NormedSpace.toModule.{0, u_1} Real V
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                        (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))))))
              (@IsBoundedSMul.toUniformContinuousConstSMul.{0, u_1} Real V
                (@SeminormedRing.toPseudoMetricSpace.{0} Real
                  (@SeminormedCommRing.toSeminormedRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real
                      (@NormedField.toNormedCommRing.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))
                (@MulZeroClass.toZero.{0} Real
                  (@instMulZeroClassOfSemiring.{0} Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                (@NegZeroClass.toZero.{u_1} V
                  (@SubNegZeroMonoid.toNegZeroClass.{u_1} V
                    (@SubtractionMonoid.toSubNegZeroMonoid.{u_1} V
                      (@SubtractionCommMonoid.toSubtractionMonoid.{u_1} V
                        (@AddCommGroup.toDivisionAddCommMonoid.{u_1} V
                          (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                (@SMulZeroClass.toSMul.{0, u_1} Real V
                  (@AddZero.toZero.{u_1} V
                    (@AddZeroClass.toAddZero.{u_1} V
                      (@AddMonoid.toAddZeroClass.{u_1} V
                        (@AddCommMonoid.toAddMonoid.{u_1} V
                          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, u_1} Real V
                    (@AddMonoid.toAddZeroClass.{u_1} V
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, u_1} Real V
                      (@Semiring.toMonoid.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                      (@Module.toDistribMulAction.{0, u_1} Real V
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                        (@NormedSpace.toModule.{0, u_1} Real V
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                          (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))))))
                (@NormedSpace.toIsBoundedSMul.{0, u_1} Real V
                  (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                  (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            (@ContinuousLinearMap.addCommGroup._proof_7.{u_1} V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@SeminormedAddCommGroup.toAddCommGroup.{u_1} V
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))
              (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{u_1} V
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))))
        (@ContinuousLinearMap.{0, 0, u_1, u_2} Real Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@DenselyNormedField.toNormedField.{0} Real
                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
          (@RingHom.id.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
          V
          (@UniformSpace.toTopologicalSpace.{u_1} V
            (@PseudoMetricSpace.toUniformSpace.{u_1} V
              (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
          (@UniformSpace.toTopologicalSpace.{u_2} W
            (@PseudoMetricSpace.toUniformSpace.{u_2} W
              (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
          (@NormedSpace.toModule.{0, u_1} Real V
            (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
            (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
          (@NormedSpace.toModule.{0, u_2} Real W
            (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
            (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))
        (fun
            (a :
              @ContinuousLinearMap.{0, 0, u_1, u_2} Real Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                (@RingHom.id.{0} Real
                  (@Semiring.toNonAssocSemiring.{0} Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                V
                (@UniformSpace.toTopologicalSpace.{u_1} V
                  (@PseudoMetricSpace.toUniformSpace.{u_1} V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
                (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
                (@UniformSpace.toTopologicalSpace.{u_2} W
                  (@PseudoMetricSpace.toUniformSpace.{u_2} W
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
                (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                (@NormedSpace.toModule.{0, u_1} Real V
                  (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                  (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
                (@NormedSpace.toModule.{0, u_2} Real W
                  (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                  (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))) =>
          @ContinuousLinearMap.{0, 0, u_2, u_1} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)) V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
        (@EquivLike.toFunLike.{(max u_2 u_1) + 1, (max u_2 u_1) + 1, (max u_2 u_1) + 1}
          (@LinearIsometryEquiv.{0, 0, max u_2 u_1, max u_2 u_1} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@starRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@starRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@RingHomInvPair.instStarRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@RingHomInvPair.instStarRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@ContinuousLinearMap.{0, 0, u_1, u_2} Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))
            (@ContinuousLinearMap.{0, 0, u_2, u_1} Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)) V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
            (@ContinuousLinearMap.toSeminormedAddCommGroup.{0, 0, u_1, u_2} Real Real V W
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@RingHomIsometric.ids.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
            (@ContinuousLinearMap.toSeminormedAddCommGroup.{0, 0, u_2, u_1} Real Real W V
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@RingHomIsometric.ids.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
            (@ContinuousLinearMap.module.{0, 0, 0, u_1, u_2} Real Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              (@smulCommClass_self.{0, u_2} Real W
                (@CommRing.toCommMonoid.{0} Real
                  (@Field.toCommRing.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
                (@DistribMulAction.toMulAction.{0, u_2} Real W
                  (@CommMonoid.toMonoid.{0} Real
                    (@CommRing.toCommMonoid.{0} Real
                      (@Field.toCommRing.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@AddCommMonoid.toAddMonoid.{u_2} W
                    (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                  (@Module.toDistribMulAction.{0, u_2} Real W
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                    (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                    (@NormedSpace.toModule.{0, u_2} Real W
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                      (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))))
              (@UniformContinuousConstSMul.instContinuousConstSMul.{0, u_2} Real W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)))
                (@SMulZeroClass.toSMul.{0, u_2} Real W
                  (@AddZero.toZero.{u_2} W
                    (@AddZeroClass.toAddZero.{u_2} W
                      (@AddMonoid.toAddZeroClass.{u_2} W
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W
                            (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                  (@DistribSMul.toSMulZeroClass.{0, u_2} Real W
                    (@AddMonoid.toAddZeroClass.{u_2} W
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))
                    (@DistribMulAction.toDistribSMul.{0, u_2} Real W
                      (@Semiring.toMonoid.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                      (@Module.toDistribMulAction.{0, u_2} Real W
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                        (@NormedSpace.toModule.{0, u_2} Real W
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                          (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))))
                (@IsBoundedSMul.toUniformContinuousConstSMul.{0, u_2} Real W
                  (@SeminormedRing.toPseudoMetricSpace.{0} Real
                    (@SeminormedCommRing.toSeminormedRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real
                        (@NormedField.toNormedCommRing.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))
                  (@MulZeroClass.toZero.{0} Real
                    (@instMulZeroClassOfSemiring.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                  (@NegZeroClass.toZero.{u_2} W
                    (@SubNegZeroMonoid.toNegZeroClass.{u_2} W
                      (@SubtractionMonoid.toSubNegZeroMonoid.{u_2} W
                        (@SubtractionCommMonoid.toSubtractionMonoid.{u_2} W
                          (@AddCommGroup.toDivisionAddCommMonoid.{u_2} W
                            (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                  (@SMulZeroClass.toSMul.{0, u_2} Real W
                    (@AddZero.toZero.{u_2} W
                      (@AddZeroClass.toAddZero.{u_2} W
                        (@AddMonoid.toAddZeroClass.{u_2} W
                          (@AddCommMonoid.toAddMonoid.{u_2} W
                            (@AddCommGroup.toAddCommMonoid.{u_2} W
                              (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                    (@DistribSMul.toSMulZeroClass.{0, u_2} Real W
                      (@AddMonoid.toAddZeroClass.{u_2} W
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))
                      (@DistribMulAction.toDistribSMul.{0, u_2} Real W
                        (@Semiring.toMonoid.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                        (@Module.toDistribMulAction.{0, u_2} Real W
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                          (@NormedSpace.toModule.{0, u_2} Real W
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                            (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))))
                  (@NormedSpace.toIsBoundedSMul.{0, u_2} Real W
                    (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                    (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@ContinuousLinearMap.addCommGroup._proof_7.{u_2} W
                (@UniformSpace.toTopologicalSpace.{u_2} W
                  (@PseudoMetricSpace.toUniformSpace.{u_2} W
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
                (@SeminormedAddCommGroup.toAddCommGroup.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))
                (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@ContinuousLinearMap.module.{0, 0, 0, u_2, u_1} Real Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              (@smulCommClass_self.{0, u_1} Real V
                (@CommRing.toCommMonoid.{0} Real
                  (@Field.toCommRing.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
                (@DistribMulAction.toMulAction.{0, u_1} Real V
                  (@CommMonoid.toMonoid.{0} Real
                    (@CommRing.toCommMonoid.{0} Real
                      (@Field.toCommRing.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@AddCommMonoid.toAddMonoid.{u_1} V
                    (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                  (@Module.toDistribMulAction.{0, u_1} Real V
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                    (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                    (@NormedSpace.toModule.{0, u_1} Real V
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                      (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))))
              (@UniformContinuousConstSMul.instContinuousConstSMul.{0, u_1} Real V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
                (@SMulZeroClass.toSMul.{0, u_1} Real V
                  (@AddZero.toZero.{u_1} V
                    (@AddZeroClass.toAddZero.{u_1} V
                      (@AddMonoid.toAddZeroClass.{u_1} V
                        (@AddCommMonoid.toAddMonoid.{u_1} V
                          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, u_1} Real V
                    (@AddMonoid.toAddZeroClass.{u_1} V
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, u_1} Real V
                      (@Semiring.toMonoid.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                      (@Module.toDistribMulAction.{0, u_1} Real V
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                        (@NormedSpace.toModule.{0, u_1} Real V
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                          (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))))))
                (@IsBoundedSMul.toUniformContinuousConstSMul.{0, u_1} Real V
                  (@SeminormedRing.toPseudoMetricSpace.{0} Real
                    (@SeminormedCommRing.toSeminormedRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real
                        (@NormedField.toNormedCommRing.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))
                  (@MulZeroClass.toZero.{0} Real
                    (@instMulZeroClassOfSemiring.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                  (@NegZeroClass.toZero.{u_1} V
                    (@SubNegZeroMonoid.toNegZeroClass.{u_1} V
                      (@SubtractionMonoid.toSubNegZeroMonoid.{u_1} V
                        (@SubtractionCommMonoid.toSubtractionMonoid.{u_1} V
                          (@AddCommGroup.toDivisionAddCommMonoid.{u_1} V
                            (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                  (@SMulZeroClass.toSMul.{0, u_1} Real V
                    (@AddZero.toZero.{u_1} V
                      (@AddZeroClass.toAddZero.{u_1} V
                        (@AddMonoid.toAddZeroClass.{u_1} V
                          (@AddCommMonoid.toAddMonoid.{u_1} V
                            (@AddCommGroup.toAddCommMonoid.{u_1} V
                              (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                    (@DistribSMul.toSMulZeroClass.{0, u_1} Real V
                      (@AddMonoid.toAddZeroClass.{u_1} V
                        (@AddCommMonoid.toAddMonoid.{u_1} V
                          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))
                      (@DistribMulAction.toDistribSMul.{0, u_1} Real V
                        (@Semiring.toMonoid.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                        (@AddCommMonoid.toAddMonoid.{u_1} V
                          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                        (@Module.toDistribMulAction.{0, u_1} Real V
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                          (@NormedSpace.toModule.{0, u_1} Real V
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                            (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))))))
                  (@NormedSpace.toIsBoundedSMul.{0, u_1} Real V
                    (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                    (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@ContinuousLinearMap.addCommGroup._proof_7.{u_1} V
                (@UniformSpace.toTopologicalSpace.{u_1} V
                  (@PseudoMetricSpace.toUniformSpace.{u_1} V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
                (@SeminormedAddCommGroup.toAddCommGroup.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))
                (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))))
          (@ContinuousLinearMap.{0, 0, u_1, u_2} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))
          (@ContinuousLinearMap.{0, 0, u_2, u_1} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@DenselyNormedField.toNormedField.{0} Real
                          (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
            W
            (@UniformSpace.toTopologicalSpace.{u_2} W
              (@PseudoMetricSpace.toUniformSpace.{u_2} W
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)) V
            (@UniformSpace.toTopologicalSpace.{u_1} V
              (@PseudoMetricSpace.toUniformSpace.{u_1} V
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
            (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
            (@NormedSpace.toModule.{0, u_2} Real W
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
            (@NormedSpace.toModule.{0, u_1} Real V
              (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
          (@LinearIsometryEquiv.instEquivLike.{0, 0, max u_2 u_1, max u_2 u_1} Real Real
            (@ContinuousLinearMap.{0, 0, u_1, u_2} Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)) W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))
            (@ContinuousLinearMap.{0, 0, u_2, u_1} Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)) V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
            (@starRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@starRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@RingHomInvPair.instStarRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@RingHomInvPair.instStarRingEnd.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@DenselyNormedField.toNormedField.{0} Real
                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
              (@RCLike.toStarRing.{0} Real Real.instRCLike))
            (@ContinuousLinearMap.toSeminormedAddCommGroup.{0, 0, u_1, u_2} Real Real V W
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@RingHomIsometric.ids.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
            (@ContinuousLinearMap.toSeminormedAddCommGroup.{0, 0, u_2, u_1} Real Real W V
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
              (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)
              (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@RingHomIsometric.ids.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
            (@ContinuousLinearMap.module.{0, 0, 0, u_1, u_2} Real Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              (@smulCommClass_self.{0, u_2} Real W
                (@CommRing.toCommMonoid.{0} Real
                  (@Field.toCommRing.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
                (@DistribMulAction.toMulAction.{0, u_2} Real W
                  (@CommMonoid.toMonoid.{0} Real
                    (@CommRing.toCommMonoid.{0} Real
                      (@Field.toCommRing.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@AddCommMonoid.toAddMonoid.{u_2} W
                    (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                  (@Module.toDistribMulAction.{0, u_2} Real W
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                    (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                    (@NormedSpace.toModule.{0, u_2} Real W
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                      (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4)))))
              (@UniformContinuousConstSMul.instContinuousConstSMul.{0, u_2} Real W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)))
                (@SMulZeroClass.toSMul.{0, u_2} Real W
                  (@AddZero.toZero.{u_2} W
                    (@AddZeroClass.toAddZero.{u_2} W
                      (@AddMonoid.toAddZeroClass.{u_2} W
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W
                            (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                  (@DistribSMul.toSMulZeroClass.{0, u_2} Real W
                    (@AddMonoid.toAddZeroClass.{u_2} W
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))
                    (@DistribMulAction.toDistribSMul.{0, u_2} Real W
                      (@Semiring.toMonoid.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                      (@AddCommMonoid.toAddMonoid.{u_2} W
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                      (@Module.toDistribMulAction.{0, u_2} Real W
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                        (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                        (@NormedSpace.toModule.{0, u_2} Real W
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                          (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))))
                (@IsBoundedSMul.toUniformContinuousConstSMul.{0, u_2} Real W
                  (@SeminormedRing.toPseudoMetricSpace.{0} Real
                    (@SeminormedCommRing.toSeminormedRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real
                        (@NormedField.toNormedCommRing.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))
                  (@MulZeroClass.toZero.{0} Real
                    (@instMulZeroClassOfSemiring.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
                  (@NegZeroClass.toZero.{u_2} W
                    (@SubNegZeroMonoid.toNegZeroClass.{u_2} W
                      (@SubtractionMonoid.toSubNegZeroMonoid.{u_2} W
                        (@SubtractionCommMonoid.toSubtractionMonoid.{u_2} W
                          (@AddCommGroup.toDivisionAddCommMonoid.{u_2} W
                            (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                  (@SMulZeroClass.toSMul.{0, u_2} Real W
                    (@AddZero.toZero.{u_2} W
                      (@AddZeroClass.toAddZero.{u_2} W
                        (@AddMonoid.toAddZeroClass.{u_2} W
                          (@AddCommMonoid.toAddMonoid.{u_2} W
                            (@AddCommGroup.toAddCommMonoid.{u_2} W
                              (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))))
                    (@DistribSMul.toSMulZeroClass.{0, u_2} Real W
                      (@AddMonoid.toAddZeroClass.{u_2} W
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))))
                      (@DistribMulAction.toDistribSMul.{0, u_2} Real W
                        (@Semiring.toMonoid.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                        (@AddCommMonoid.toAddMonoid.{u_2} W
                          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3)))
                        (@Module.toDistribMulAction.{0, u_2} Real W
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@DenselyNormedField.toNormedField.{0} Real
                                    (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                          (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
                          (@NormedSpace.toModule.{0, u_2} Real W
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                            (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))))
                  (@NormedSpace.toIsBoundedSMul.{0, u_2} Real W
                    (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                    (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))))
              (@RingHom.id.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))))
              (@ContinuousLinearMap.addCommGroup._proof_7.{u_2} W
                (@UniformSpace.toTopologicalSpace.{u_2} W
                  (@PseudoMetricSpace.toUniformSpace.{u_2} W
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
                (@SeminormedAddCommGroup.toAddCommGroup.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))
                (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{u_2} W
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
            (@ContinuousLinearMap.module.{0, 0, 0, u_2, u_1} Real Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
              W
              (@UniformSpace.toTopologicalSpace.{u_2} W
                (@PseudoMetricSpace.toUniformSpace.{u_2} W
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_2} W
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3))))
              (@AddCommGroup.toAddCommMonoid.{u_2} W (@NormedAddCommGroup.toAddCommGroup.{u_2} W inst_3))
              (@NormedSpace.toModule.{0, u_2} Real W
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real W Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} W inst_3) inst_4))
              V
              (@UniformSpace.toTopologicalSpace.{u_1} V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst))))
              (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              (@NormedSpace.toModule.{0, u_1} Real V
                (@DenselyNormedField.toNormedField.{0} Real (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1))
              (@smulCommClass_self.{0, u_1} Real V
                (@CommRing.toCommMonoid.{0} Real
                  (@Field.toCommRing.{0} Real
                    (@NormedField.toField.{0} Real
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
                (@DistribMulAction.toMulAction.{0, u_1} Real V
                  (@CommMonoid.toMonoid.{0} Real
                    (@CommRing.toCommMonoid.{0} Real
                      (@Field.toCommRing.{0} Real
                        (@NormedField.toField.{0} Real
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                  (@AddCommMonoid.toAddMonoid.{u_1} V
                    (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                  (@Module.toDistribMulAction.{0, u_1} Real V
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@DenselyNormedField.toNormedField.{0} Real
                              (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                    (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                    (@NormedSpace.toModule.{0, u_1} Real V
                      (@DenselyNormedField.toNormedField.{0} Real
                        (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                      (@InnerProductSpace.toNormedSpace.{0, u_1} Real V Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst) inst_1)))))
              (@UniformContinuousConstSMul.instContinuousConstSMul.{0, u_1} Real V
                (@PseudoMetricSpace.toUniformSpace.{u_1} V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)))
                (@SMulZeroClass.toSMul.{0, u_1} Real V
                  (@AddZero.toZero.{u_1} V
                    (@AddZeroClass.toAddZero.{u_1} V
                      (@AddMonoid.toAddZeroClass.{u_1} V
                        (@AddCommMonoid.toAddMonoid.{u_1} V
                          (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, u_1} Real V
                    (@AddMonoid.toAddZeroClass.{u_1} V
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, u_1} Real V
                      (@Semiring.toMonoid.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))))
                      (@AddCommMonoid.toAddMonoid.{u_1} V
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst)))
                      (@Module.toDistribMulAction.{0, u_1} Real V
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@DenselyNormedField.toNormedField.{0} Real
                                  (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))))))
                        (@AddCommGroup.toAddCommMonoid.{u_1} V (@NormedAddCommGroup.toAddCommGroup.{u_1} V inst))
                        (@NormedSpace.toModule.{0, u_1} Real V
                          (@DenselyNormedField.toNormedField.{0} Real
                            (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} V inst)
                          (@InnerProductSpace.toNormedSpace.{0, u_1} _ _ _ _ _))))))
                _)
              _ _)))
        _ _)
      _;
  _

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"physical_fixed_noise_information\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .argument, .body, .argument, .body, .argument, .argument, .body, .body, .body, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"physical_fixed_noise_information\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration.{u_1, u_2}).actual (Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"PhysicalFixedNoiseInformation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation, declaration := `Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
