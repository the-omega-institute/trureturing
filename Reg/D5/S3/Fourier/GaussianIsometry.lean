import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.GaussianIsometry
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u t s r o a

namespace Reg.D5.S3.Fourier.GaussianIsometry
open _root_.D5.S3.Fourier.GaussianIsometry

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ≥0
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => Measure ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : Empty → Unit → ℝ≥0 := fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => gaussianReal 0 x) emptyAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => gaussianReal 1 0) emptyAnchor

def theoremLaw (R : Realization signature.{u}) : Prop := ∀ (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H],
    ∃ (ι : Type u)
      (W : H →ₗᵢ[ℝ] Lp ℝ 2 (Measure.infinitePi (fun _ : ι => gaussianReal 0 1))),
      (∀ h : H, HasLaw (fun ω => W h ω) (R.readout ⟨()⟩ () (‖h‖ ^ 2).toNNReal)
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1))) ∧
      IsGaussianProcess (fun h ω => W h ω)
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) ∧
      ∀ h k, cov[fun ω => W h ω, fun ω => W k ω;
        Measure.infinitePi (fun _ : ι => gaussianReal 0 1)] = ⟪h, k⟫

def arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _
  exact exists_gaussian_isometry H

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨ι, W, hw, _⟩ := h (lp (fun _ : ULift.{u} Unit => ℝ) 2)
  have hz := hw 0
  have he : (fun ω => W 0 ω) =ᵐ[Measure.infinitePi (fun _ : ι => gaussianReal 0 1)]
      (fun _ => (0 : ℝ)) := by
    rw [map_zero]
    exact Lp.coeFn_zero _ _ _
  have hz' := hz.congr he.symm
  have hi := hz'.integral_eq
  norm_num [rejected, realize, integral_id_gaussianReal] at hi

theorem dependence_proof : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hv := congrArg (fun μ : Measure ℝ => variance (fun x : ℝ => x) μ) h
  norm_num [actual, realize, variance_id_gaussianReal] at hv

private theorem sensitivity_of_rejected
    (A : Arena.{t, s, r, o, a}) (x y : Realization A.signature)
    (hrole : ∀ i j : A.signature.Role, j = i)
    (hanchor : x.anchor = y.anchor)
    (hempty : ∀ _ : A.signature.Anchor, False)
    (hbad : ¬ A.Law y) : Sensitivity A x := by
  constructor
  · intro i
    exact ⟨y, fun j h => (h (hrole i j)).elim, hanchor, hbad⟩
  · intro i
    exact (hempty i).elim

private theorem roles_equal (i j : signature.{u}.Role) : j = i :=
  @Subsingleton.elim (ULift.{u} Unit) _ j i

private theorem anchors_equal : actual.{u}.anchor = rejected.anchor := rfl

private theorem anchors_empty (i : signature.{u}.Anchor) : False := nomatch i

theorem sensitivity_proof : Sensitivity arena.{u} actual :=
  sensitivity_of_rejected arena actual rejected roles_equal
    anchors_equal anchors_empty.{u} rejected_law

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.GaussianIsometry.exists_gaussian_isometry.{u}) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => gaussianReal 0 x) emptyAnchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "GaussianIsometry") "exists_gaussian_isometry") "Reg.D5.S3.Fourier.GaussianIsometry/Reg.D5.S3.Fourier.GaussianIsometry.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.GaussianIsometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => gaussianReal 0 x) emptyAnchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.GaussianIsometry, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.GaussianIsometry, declaration := `D5.S3.Fourier.GaussianIsometry.exists_gaussian_isometry, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.observationFact0, `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.anchorEnumeration }


end Reg.D5.S3.Fourier.GaussianIsometry


noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Fourier.GaussianIsometry.arena.{u}
noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Fourier.GaussianIsometry.arena.{u}
noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
  Reg.D5.S3.Fourier.GaussianIsometry.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u, 0, 0}
    Reg.D5.S3.Fourier.GaussianIsometry.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
      Reg.D5.S3.Fourier.GaussianIsometry.arena.{u} Reg.D5.S3.Fourier.GaussianIsometry.actual.{u})
    Reg.D5.S3.Fourier.GaussianIsometry.registration.{u})

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"exists_gaussian_isometry\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Fourier.GaussianIsometry, declaration := `D5.S3.Fourier.GaussianIsometry.exists_gaussian_isometry, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u, 0, 0}
  Reg.D5.S3.Fourier.GaussianIsometry.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
    Reg.D5.S3.Fourier.GaussianIsometry.arena.{u} Reg.D5.S3.Fourier.GaussianIsometry.actual.{u})
  Reg.D5.S3.Fourier.GaussianIsometry.registration.{u})

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.roleEnumeration.{u} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u, 0} Unit) where
  values := [@ULift.up.{u, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.observation0.{u} : (H : Type u) →
  [inst : NormedAddCommGroup.{u} H] →
    [inst_1 :
        @InnerProductSpace.{0, u} Real H Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)] →
      [@CompleteSpace.{u} H
            (@PseudoMetricSpace.toUniformSpace.{u} H
              (@SeminormedAddCommGroup.toPseudoMetricSpace.{u} H
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)))] →
        (ι : Type u) →
          (W :
              @LinearIsometry.{0, 0, u, u} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) H
                (@Subtype.{u + 1}
                  (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                    (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                    (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                      (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                      ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                  fun
                    (x :
                      @MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                        (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                        (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                          (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                          ProbabilityTheory.gaussianReal
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))) =>
                  @Membership.mem.{u, u}
                    (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                      (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real
                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                      (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                        (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                        ProbabilityTheory.gaussianReal
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                    (@AddSubgroup.{u}
                      (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                        (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                        (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                          (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                          ProbabilityTheory.gaussianReal
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                      (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                        (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                        (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                          (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                          ProbabilityTheory.gaussianReal
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                        (@AddCommGroup.toAddGroup.{0} Real
                          (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                        (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                    (@SetLike.instMembership.{u, u}
                      (@AddSubgroup.{u}
                        (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                        (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@AddCommGroup.toAddGroup.{0} Real
                            (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                          (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                      (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                        (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                        (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                          (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                          ProbabilityTheory.gaussianReal
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                      (@AddSubgroup.instSetLike.{u}
                        (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                        (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@AddCommGroup.toAddGroup.{0} Real
                            (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                          (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)))))
                    (@MeasureTheory.Lp.{0, u} ((i : ι) → Real) Real
                      (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                      Real.normedAddCommGroup
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                        (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                        ProbabilityTheory.gaussianReal
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                    x)
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u}
                  (@Subtype.{u + 1}
                    (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                      (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real
                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                      (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                        (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                        ProbabilityTheory.gaussianReal
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                    fun
                      (x :
                        @MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))) =>
                    @Membership.mem.{u, u}
                      (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                        (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real
                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                        (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                          (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                          ProbabilityTheory.gaussianReal
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                      (@AddSubgroup.{u}
                        (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                        (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@AddCommGroup.toAddGroup.{0} Real
                            (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                          (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                      (@SetLike.instMembership.{u, u}
                        (@AddSubgroup.{u}
                          (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                            (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                            (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                              (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                              ProbabilityTheory.gaussianReal
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                          (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                            (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                            (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                              (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                              ProbabilityTheory.gaussianReal
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                            (@AddCommGroup.toAddGroup.{0} Real
                              (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                            (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                        (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real
                              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                            (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                            ProbabilityTheory.gaussianReal
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                        (@AddSubgroup.instSetLike.{u}
                          (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                            (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                            (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                              (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                              ProbabilityTheory.gaussianReal
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                          (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                            (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                            (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                              (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                              ProbabilityTheory.gaussianReal
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                            (@AddCommGroup.toAddGroup.{0} Real
                              (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                            (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)))))
                      (@MeasureTheory.Lp.{0, u} ((i : ι) → Real) Real
                        (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                        Real.normedAddCommGroup
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                          (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                          ProbabilityTheory.gaussianReal
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                      x)
                  (@MeasureTheory.Lp.instNormedAddCommGroup.{u, 0} ((i : ι) → Real) Real
                    (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                      (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                      ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                    Real.normedAddCommGroup fact_one_le_two_ennreal))
                (@NormedSpace.toModule.{0, u} Real H Real.normedField
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)
                  (@InnerProductSpace.toNormedSpace.{0, u} Real H Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst) inst_1))
                (@MeasureTheory.Lp.instModule.{u, 0, 0} ((i : ι) → Real) Real Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                  Real.normedAddCommGroup (@NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)
                  (@Semiring.toModule.{0} Real
                    (@Ring.toSemiring.{0} Real
                      (@NormedRing.toRing.{0} Real (@NormedCommRing.toNormedRing.{0} Real Real.normedCommRing))))
                  Real.isBoundedSMul)) →
            (h : H) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u, 0, 0}
                Reg.D5.S3.Fourier.GaussianIsometry.signature.{u} (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun (H : Type u) [inst : NormedAddCommGroup.{u} H]
    [@InnerProductSpace.{0, u} Real H Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)]
    [@CompleteSpace.{u} H
        (@PseudoMetricSpace.toUniformSpace.{u} H
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u} H
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)))]
    (ι : Type u)
    (W :
      @LinearIsometry.{0, 0, u, u} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) H
        (@Subtype.{u + 1}
          (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
            (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
            (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
              fun (x : ι) =>
              ProbabilityTheory.gaussianReal (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
          fun
            (x :
              @MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                  fun (x : ι) =>
                  ProbabilityTheory.gaussianReal
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))) =>
          @Membership.mem.{u, u}
            (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
              (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
              (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                fun (x : ι) =>
                ProbabilityTheory.gaussianReal
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
            (@AddSubgroup.{u}
              (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                  fun (x : ι) =>
                  ProbabilityTheory.gaussianReal
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
              (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                  fun (x : ι) =>
                  ProbabilityTheory.gaussianReal
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                (@AddCommGroup.toAddGroup.{0} Real
                  (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
            (@SetLike.instMembership.{u, u}
              (@AddSubgroup.{u}
                (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@AddCommGroup.toAddGroup.{0} Real
                    (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                  (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
              (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                  fun (x : ι) =>
                  ProbabilityTheory.gaussianReal
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
              (@AddSubgroup.instSetLike.{u}
                (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@AddCommGroup.toAddGroup.{0} Real
                    (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                  (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)))))
            (@MeasureTheory.Lp.{0, u} ((i : ι) → Real) Real
              (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
              Real.normedAddCommGroup
              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                fun (x : ι) =>
                ProbabilityTheory.gaussianReal
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
            x)
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u}
          (@Subtype.{u + 1}
            (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
              (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
              (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                fun (x : ι) =>
                ProbabilityTheory.gaussianReal
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
            fun
              (x :
                @MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))) =>
            @Membership.mem.{u, u}
              (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                  fun (x : ι) =>
                  ProbabilityTheory.gaussianReal
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
              (@AddSubgroup.{u}
                (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@AddCommGroup.toAddGroup.{0} Real
                    (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                  (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
              (@SetLike.instMembership.{u, u}
                (@AddSubgroup.{u}
                  (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                    (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                    (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                      (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                      ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                  (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                    (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                    (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                      (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                      ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                    (@AddCommGroup.toAddGroup.{0} Real
                      (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                    (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                  (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                  (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                    (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                    ProbabilityTheory.gaussianReal
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                (@AddSubgroup.instSetLike.{u}
                  (@MeasureTheory.AEEqFun.{u, 0} ((i : ι) → Real) Real
                    (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                    (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                      (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                      ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
                  (@MeasureTheory.AEEqFun.instAddGroup.{u, 0} ((i : ι) → Real) Real
                    (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                    (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real)
                      (fun (i : ι) => Real.measurableSpace) fun (x : ι) =>
                      ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))))
                    (@AddCommGroup.toAddGroup.{0} Real
                      (@NormedAddCommGroup.toAddCommGroup.{0} Real Real.normedAddCommGroup))
                    (@SeminormedAddCommGroup.toIsTopologicalAddGroup.{0} Real
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)))))
              (@MeasureTheory.Lp.{0, u} ((i : ι) → Real) Real
                (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
                Real.normedAddCommGroup
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
                  fun (x : ι) =>
                  ProbabilityTheory.gaussianReal
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))))
              x)
          (@MeasureTheory.Lp.instNormedAddCommGroup.{u, 0} ((i : ι) → Real) Real
            (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
              fun (x : ι) =>
              ProbabilityTheory.gaussianReal (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
            Real.normedAddCommGroup fact_one_le_two_ennreal))
        (@NormedSpace.toModule.{0, u} Real H Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst)
          (@InnerProductSpace.toNormedSpace.{0, u} Real H Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u} H inst) inst_1))
        (@MeasureTheory.Lp.instModule.{u, 0, 0} ((i : ι) → Real) Real Real
          (@MeasurableSpace.pi.{u, 0} ι (fun (x : ι) => Real) fun (i : ι) => Real.measurableSpace)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@MeasureTheory.Measure.infinitePi.{u, 0} ι (fun (x : ι) => Real) (fun (i : ι) => Real.measurableSpace)
            fun (x : ι) =>
            ProbabilityTheory.gaussianReal (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
          Real.normedAddCommGroup (@NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)
          (@Semiring.toModule.{0} Real
            (@Ring.toSemiring.{0} Real
              (@NormedRing.toRing.{0} Real (@NormedCommRing.toNormedRing.{0} Real Real.normedCommRing))))
          Real.isBoundedSMul))
    (h : H) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u, 0, 0}
    Reg.D5.S3.Fourier.GaussianIsometry.signature.{u} Reg.D5.S3.Fourier.GaussianIsometry.actual.{u}
    (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1}
    (Real.toNNReal
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Norm.norm.{u} H (@NormedAddCommGroup.toNorm.{u} H inst) h)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"exists_gaussian_isometry\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Fourier.GaussianIsometry, declaration := `D5.S3.Fourier.GaussianIsometry.exists_gaussian_isometry, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .body, .function, .argument, .body, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.GaussianIsometry.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"exists_gaussian_isometry\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Fourier.GaussianIsometry, declaration := `D5.S3.Fourier.GaussianIsometry.exists_gaussian_isometry, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.GaussianIsometry.registration.{u}).actual (Reg.D5.S3.Fourier.GaussianIsometry.registration.{u}).variation.2.choose (Reg.D5.S3.Fourier.GaussianIsometry.registration.{u}).variation.1 (Reg.D5.S3.Fourier.GaussianIsometry.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.GaussianIsometry.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"GaussianIsometry\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Fourier.GaussianIsometry, declaration := `Reg.D5.S3.Fourier.GaussianIsometry.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
