import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
open Filter MeasureTheory Set TopologicalSpace Topology
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

abbrev signature : Signature where
  Params := Σ I : Type u, I → Circle
  State p := C((Subgroup.zpowers p.2).topologicalClosure, ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C((Subgroup.zpowers p.2).topologicalClosure, ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The full source statement; the intervention changes only orbit observations.
The subgroup equality and the integral of the original observable remain fixed. -/
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {I : Type u} [Fintype I] (g : I → Circle),
    let G := (Subgroup.zpowers g).topologicalClosure
    letI : CompactSpace G := isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
    (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) ∧
    ∀ f : C(G, ℂ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (r.readout () ⟨I, g⟩ f) ⟨g ^ (n + 1),
        G.pow_mem (subset_closure (Subgroup.mem_zpowers g)) (n + 1)⟩) / (N : ℂ))
      atTop (𝓝 (∫ z : G, f z ∂μ))

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let I := ULift.{u} Unit
  let g : I → Circle := 1
  let G := (Subgroup.zpowers g).topologicalClosure
  letI : CompactSpace G := isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  letI : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have ht := (h g).2 (1 : C(G, ℂ))
  have hz : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa [rejected, realize, signature, μ] using ht
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hz)

def registration : Registration arena.{u}
    (∀ {I : Type u} [Fintype I] (g : I → Circle),
      let G := (Subgroup.zpowers g).topologicalClosure
      letI : CompactSpace G := isCompact_iff_compactSpace.mp
        (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
      letI : MeasurableSpace G := borel G
      letI : BorelSpace G := ⟨rfl⟩
      let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
      (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) ∧
      ∀ f : C(G, ℂ), Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, f ⟨g ^ (n + 1),
          G.pow_mem (subset_closure (Subgroup.mem_zpowers g)) (n + 1)⟩) / (N : ℂ))
        atTop (𝓝 (∫ z : G, f z ∂μ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    let G := (Subgroup.zpowers (1 : ULift.{u} Unit → Circle)).topologicalClosure
    refine ⟨⟨ULift.{u} Unit, 1⟩, (0 : C(G, ℂ)), (1 : C(G, ℂ)), ?_⟩
    intro h
    have hv := congrArg (fun f : C(G, ℂ) => f 1) h
    exact (zero_ne_one : (0 : ℂ) ≠ 1) hv

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ f => f) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "TorusOrbitEquidistribution") "result") "Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution/Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ f => f) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, definition := none, coordinates := #[0, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "fn", "arg", "body", "fn", "arg", "arg", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution


noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.arena.) (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.observation0.{u_1} : {I : Type u_1} →
  [Fintype.{u_1} I] →
    (g : I → Circle) →
      let G :
        @Subgroup.{u_1} (I → Circle)
          (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
            @CommGroup.toGroup.{0} Circle Circle.instCommGroup) :=
        @Subgroup.topologicalClosure.{u_1} (I → Circle)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
          (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
            @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
          (@Pi.topologicalGroup.{u_1, 0} I (fun (a : I) => Circle) (fun (i : I) => instTopologicalSpaceCircle)
            (fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup) fun (b : I) =>
            Circle.instIsTopologicalGroup)
          (@Subgroup.zpowers.{u_1} (I → Circle)
            (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
              @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
            g);
      (f :
          @ContinuousMap.{u_1, 0}
            (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            Complex
            (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
              (fun (x : I → Circle) =>
                @Membership.mem.{u_1, u_1} (I → Circle)
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                    (I → Circle)
                    (@Subgroup.instSetLike.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                  G x)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
            (@UniformSpace.toTopologicalSpace.{0} Complex
              (@PseudoMetricSpace.toUniformSpace.{0} Complex
                (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                  (@SeminormedCommRing.toSeminormedRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))) →
        (N n : Nat) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
            Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.signature.{u_1} PUnit.unit.{1}
            (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (I : Type u_1) => I → Circle) I g) :=
  fun {I : Type u_1} [Fintype.{u_1} I] (g : I → Circle) =>
  let G :
    @Subgroup.{u_1} (I → Circle)
      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
        @CommGroup.toGroup.{0} Circle Circle.instCommGroup) :=
    @Subgroup.topologicalClosure.{u_1} (I → Circle)
      (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
      (@Pi.topologicalGroup.{u_1, 0} I (fun (a : I) => Circle) (fun (i : I) => instTopologicalSpaceCircle)
        (fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup) fun (b : I) =>
        Circle.instIsTopologicalGroup)
      (@Subgroup.zpowers.{u_1} (I → Circle)
        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
        g);
  have μ :
    @MeasureTheory.Measure.{u_1}
      (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
        @Membership.mem.{u_1, u_1} (I → Circle)
          (@Subgroup.{u_1} (I → Circle)
            (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
              @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
          (@SetLike.instMembership.{u_1, u_1}
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (I → Circle)
            (@Subgroup.instSetLike.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
          G x)
      (@borel.{u_1}
        (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
          @Membership.mem.{u_1, u_1} (I → Circle)
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (I → Circle)
              (@Subgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
            G x)
        (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
          (fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))) :=
    @MeasureTheory.Measure.haarMeasure.{u_1}
      (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
        @Membership.mem.{u_1, u_1} (I → Circle)
          (@Subgroup.{u_1} (I → Circle)
            (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
              @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
          (@SetLike.instMembership.{u_1, u_1}
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (I → Circle)
            (@Subgroup.instSetLike.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
          G x)
      (@Subgroup.toGroup.{u_1} (I → Circle)
        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
        G)
      (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
        (fun (x : I → Circle) =>
          @Membership.mem.{u_1, u_1} (I → Circle)
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (I → Circle)
              (@Subgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
            G x)
        (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
      (@Subgroup.instIsTopologicalGroupSubtypeMem.{u_1} (I → Circle)
        (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
        (@Pi.topologicalGroup.{u_1, 0} I (fun (a : I) => Circle) (fun (i : I) => instTopologicalSpaceCircle)
          (fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup) fun (b : I) =>
          Circle.instIsTopologicalGroup)
        G)
      (@borel.{u_1}
        (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
          @Membership.mem.{u_1, u_1} (I → Circle)
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (I → Circle)
              (@Subgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
            G x)
        (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
          (fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
      (@BorelSpace.mk.{u_1}
        (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
          @Membership.mem.{u_1, u_1} (I → Circle)
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (I → Circle)
              (@Subgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
            G x)
        (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
          (fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
        (@borel.{u_1}
          (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
            (fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
        (@rfl.{u_1 + 1}
          (MeasurableSpace.{u_1}
            (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x))
          (@borel.{u_1}
            (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
              (fun (x : I → Circle) =>
                @Membership.mem.{u_1, u_1} (I → Circle)
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                    (I → Circle)
                    (@Subgroup.instSetLike.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                  G x)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))))
      (@Top.top.{u_1}
        (@TopologicalSpace.PositiveCompacts.{u_1}
          (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
            (fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
        (@TopologicalSpace.PositiveCompacts.instTopOfCompactSpaceOfNonempty.{u_1}
          (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
            (fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
          (@Iff.mp
            (@IsCompact.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
              (@SetLike.coe.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                G))
            (@CompactSpace.{u_1}
              (@Set.Elem.{u_1} (I → Circle)
                (@SetLike.coe.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  G))
              (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
                (fun (x : I → Circle) =>
                  @Membership.mem.{u_1, u_1} (I → Circle) (Set.{u_1} (I → Circle))
                    (@Set.instMembership.{u_1} (I → Circle))
                    (@SetLike.coe.{u_1, u_1}
                      (@Subgroup.{u_1} (I → Circle)
                        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                          @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                      (I → Circle)
                      (@Subgroup.instSetLike.{u_1} (I → Circle)
                        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                          @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                      G)
                    x)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
            (@isCompact_iff_compactSpace.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
              (@SetLike.coe.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                G))
            (@IsClosed.isCompact.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
              (@SetLike.coe.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@Subgroup.topologicalClosure.{u_1} (I → Circle)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                  (@Pi.topologicalGroup.{u_1, 0} I (fun (a : I) => Circle) (fun (i : I) => instTopologicalSpaceCircle)
                    (fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup) fun (b : I) =>
                    Circle.instIsTopologicalGroup)
                  (@Subgroup.zpowers.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                    g)))
              (@Function.compactSpace.{0, u_1} Circle I instTopologicalSpaceCircle Circle.instCompactSpace)
              (@Subgroup.isClosed_topologicalClosure.{u_1} (I → Circle)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalGroup.{u_1, 0} I (fun (a : I) => Circle) (fun (i : I) => instTopologicalSpaceCircle)
                  (fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup) fun (b : I) =>
                  Circle.instIsTopologicalGroup)
                (@Subgroup.zpowers.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                  g))))
          (@Torsor.nonempty.{u_1, u_1}
            (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
              @Membership.mem.{u_1, u_1} (I → Circle)
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (I → Circle)
                  (@Subgroup.instSetLike.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                G x)
            (@Subgroup.toGroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
              G)
            (@Group.instTorsor.{u_1}
              (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
                @Membership.mem.{u_1, u_1} (I → Circle)
                  (@Subgroup.{u_1} (I → Circle)
                    (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                      @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                    (I → Circle)
                    (@Subgroup.instSetLike.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
                  G x)
              (@Subgroup.toGroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                G)))));
  fun
    (f :
      @ContinuousMap.{u_1, 0}
        (@Subtype.{u_1 + 1} (I → Circle) fun (x : I → Circle) =>
          @Membership.mem.{u_1, u_1} (I → Circle)
            (@Subgroup.{u_1} (I → Circle)
              (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (I → Circle)
              (@Subgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
            G x)
        Complex
        (@instTopologicalSpaceSubtype.{u_1} (I → Circle)
          (fun (x : I → Circle) =>
            @Membership.mem.{u_1, u_1} (I → Circle)
              (@Subgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup))
                (I → Circle)
                (@Subgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)))
              G x)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))
    (N n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.signature.{u_1}
    Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (I : Type u_1) => I → Circle) I g) f

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"argument\",\"body\",\"function\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result, part := .type, path := [.body, .body, .body, .letBody, .letBody, .argument, .body, .function, .function, .argument, .body, .function, .argument, .argument, .body, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration.{u_1}).actual (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration.{u_1}).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration.{u_1}).variation.1 (Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusOrbitEquidistribution\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
