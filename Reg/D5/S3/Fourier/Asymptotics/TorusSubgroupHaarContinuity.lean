import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
open Filter MeasureTheory Set
open scoped Topology
open _root_.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

private abbrev full (I : Type u) : ClosedSubgroup (I → Circle) :=
  ⟨⊤, isClosed_univ⟩

private abbrev trivial (I : Type u) : ClosedSubgroup (I → Circle) :=
  ⟨⊥, isClosed_singleton⟩

abbrev signature : Signature where
  Params := Type u
  State I := ClosedSubgroup (I → Circle)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := ClosedSubgroup (I → Circle)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ H => H) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ I _ => trivial I) (fun e => nomatch e)

/-- The original Hausdorff premise, dictionaries and both probability-measure topologies
are fixed. Only the subgroup occurrence in the limiting ambient Haar measure is read out. -/
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {I : Type u} [Fintype I]
    (Hn : ℕ → ClosedSubgroup (I → Circle)) (H : ClosedSubgroup (I → Circle)),
    Tendsto (fun n => Metric.hausdorffDist (Hn n : Set (I → Circle))
      (H : Set (I → Circle))) atTop (𝓝 0) →
    letI : MeasurableSpace (I → Circle) := borel _
    letI : BorelSpace (I → Circle) := ⟨rfl⟩
    Tendsto (fun n => ambientHaar (Hn n)) atTop (𝓝 (ambientHaar (r.readout () I H)))

/-- The coordinate character separates full-torus Haar from trivial-subgroup Haar. -/
theorem top_ne_bot :
    ambientHaar (full (ULift.{u} Unit)) ≠ ambientHaar (trivial (ULift.{u} Unit)) := by
  let I := ULift.{u} Unit
  letI : MeasurableSpace (I → Circle) := borel _
  letI : BorelSpace (I → Circle) := ⟨rfl⟩
  let (K : ClosedSubgroup (I → Circle)) : MeasurableSpace K := borel K
  let (K : ClosedSubgroup (I → Circle)) : BorelSpace K := ⟨rfl⟩
  let (K : ClosedSubgroup (I → Circle)) : IsTopologicalGroup K :=
    inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let μ (K : ClosedSubgroup (I → Circle)) : Measure K := Measure.haarMeasure ⊤
  let (K : ClosedSubgroup (I → Circle)) : IsProbabilityMeasure (μ K) :=
    ⟨Measure.haarMeasure_self⟩
  let f : (I → Circle) → ℂ := fun z => (z ⟨()⟩ : ℂ)
  have hf : Continuous f := by fun_prop
  have hmap (K : ClosedSubgroup (I → Circle)) :
      ∫ x, f x ∂(ambientHaar K : Measure (I → Circle)) = ∫ x : K, f x ∂μ K :=
    integral_map continuous_subtype_val.measurable.aemeasurable
      hf.aestronglyMeasurable
  have hb : (∫ x : (trivial I), f x ∂μ (trivial I)) = 1 := by
    apply integral_eq_const
    apply Eventually.of_forall
    intro x
    have hx : (x : I → Circle) = 1 := x.property
    simp [f, hx]
  have ht : (∫ x : (full I), f x ∂μ (full I)) = 0 := by
    let a : (full I) := ⟨fun _ => -1, Set.mem_univ _⟩
    have h := integral_mul_left_eq_self (μ := μ (full I))
      (fun x : (full I) => f x) a
    have he : (fun x : (full I) => f ((a * x : full I) : I → Circle)) =
        (fun x : (full I) => (-1 : ℂ) * f x) := by
      funext x
      simp [f, a]
    rw [he, integral_const_mul] at h
    linear_combination - (1 / 2 : ℂ) * h
  intro h
  have hi := congrArg (fun ν : @ProbabilityMeasure (I → Circle) (borel _) =>
    ∫ x, f x ∂(ν : Measure (I → Circle))) h
  rw [hmap, hmap, ht, hb] at hi
  exact zero_ne_one hi

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let I := ULift.{u} Unit
  letI : MeasurableSpace (I → Circle) := borel _
  letI : BorelSpace (I → Circle) := ⟨rfl⟩
  have ht := h (fun _ => (full I)) (full I) (by
    simp only [Metric.hausdorffDist_self_zero]
    exact tendsto_const_nhds)
  change Tendsto (fun _ : ℕ => ambientHaar (full I))
    atTop (𝓝 (ambientHaar (trivial I))) at ht
  exact top_ne_bot (tendsto_nhds_unique tendsto_const_nhds ht)

def registration : Registration arena.{u}
    (∀ {I : Type u} [Fintype I]
      (Hn : ℕ → ClosedSubgroup (I → Circle)) (H : ClosedSubgroup (I → Circle)),
      Tendsto (fun n => Metric.hausdorffDist (Hn n : Set (I → Circle))
        (H : Set (I → Circle))) atTop (𝓝 0) →
      letI : MeasurableSpace (I → Circle) := borel _
      letI : BorelSpace (I → Circle) := ⟨rfl⟩
      Tendsto (fun n => ambientHaar (Hn n)) atTop (𝓝 (ambientHaar H))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result,
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
    refine ⟨ULift.{u} Unit, full (ULift.{u} Unit), trivial (ULift.{u} Unit), ?_⟩
    intro h
    exact top_ne_bot (congrArg ambientHaar h)

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ H => H) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "TorusSubgroupHaarContinuity") "result") "Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity/Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ H => H) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity


noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.arena.{u_1}
    (∀ {I : Type u_1} [inst : Fintype.{u_1} I]
      (Hn :
        Nat →
          @ClosedSubgroup.{u_1} (I → Circle)
            (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
              @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
      (H :
        @ClosedSubgroup.{u_1} (I → Circle)
          (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
            @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)),
      @Filter.Tendsto.{0, 0} Nat Real
          (fun (n : Nat) =>
            @Metric.hausdorffDist.{u_1} (I → Circle)
              (@pseudoMetricSpacePi.{u_1, 0} I (fun (a : I) => Circle) inst fun (b : I) =>
                @MetricSpace.toPseudoMetricSpace.{0} Circle Circle.instMetricSpace)
              (@SetLike.coe.{u_1, u_1}
                (@ClosedSubgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                (I → Circle)
                (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                (Hn n))
              (@SetLike.coe.{u_1, u_1}
                (@ClosedSubgroup.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                (I → Circle)
                (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                  (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                    @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                H))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        @Filter.Tendsto.{0, u_1} Nat
          (@MeasureTheory.ProbabilityMeasure.{u_1} (I → Circle)
            (@borel.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
          (fun (n : Nat) => @D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.ambientHaar.{u_1} I inst (Hn n))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{u_1}
            (@MeasureTheory.ProbabilityMeasure.{u_1} (I → Circle)
              (@borel.{u_1} (I → Circle)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
            (@MeasureTheory.ProbabilityMeasure.instTopologicalSpace.{u_1} (I → Circle)
              (@borel.{u_1} (I → Circle)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
              (@BorelSpace.opensMeasurable.{u_1} (I → Circle)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
                (@borel.{u_1} (I → Circle)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                (@BorelSpace.mk.{u_1} (I → Circle)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
                  (@borel.{u_1} (I → Circle)
                    (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                  (@rfl.{u_1 + 1} (MeasurableSpace.{u_1} (I → Circle))
                    (@borel.{u_1} (I → Circle)
                      (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) =>
                        instTopologicalSpaceCircle))))))
            (@D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.ambientHaar.{u_1} I inst H)))
    Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration.{u_1})

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.arena.{u_1}
  (∀ {I : Type u_1} [inst : Fintype.{u_1} I]
    (Hn :
      Nat →
        @ClosedSubgroup.{u_1} (I → Circle)
          (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
            @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
    (H :
      @ClosedSubgroup.{u_1} (I → Circle)
        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
        (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)),
    @Filter.Tendsto.{0, 0} Nat Real
        (fun (n : Nat) =>
          @Metric.hausdorffDist.{u_1} (I → Circle)
            (@pseudoMetricSpacePi.{u_1, 0} I (fun (a : I) => Circle) inst fun (b : I) =>
              @MetricSpace.toPseudoMetricSpace.{0} Circle Circle.instMetricSpace)
            (@SetLike.coe.{u_1, u_1}
              (@ClosedSubgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (I → Circle)
              (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (Hn n))
            (@SetLike.coe.{u_1, u_1}
              (@ClosedSubgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (I → Circle)
              (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              H))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      @Filter.Tendsto.{0, u_1} Nat
        (@MeasureTheory.ProbabilityMeasure.{u_1} (I → Circle)
          (@borel.{u_1} (I → Circle)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
        (fun (n : Nat) => @D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.ambientHaar.{u_1} I inst (Hn n))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{u_1}
          (@MeasureTheory.ProbabilityMeasure.{u_1} (I → Circle)
            (@borel.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)))
          (@MeasureTheory.ProbabilityMeasure.instTopologicalSpace.{u_1} (I → Circle)
            (@borel.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
            (@BorelSpace.opensMeasurable.{u_1} (I → Circle)
              (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
              (@borel.{u_1} (I → Circle)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (@BorelSpace.mk.{u_1} (I → Circle)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)
                (@borel.{u_1} (I → Circle)
                  (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
                (@rfl.{u_1 + 1} (MeasurableSpace.{u_1} (I → Circle))
                  (@borel.{u_1} (I → Circle)
                    (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) =>
                      instTopologicalSpaceCircle))))))
          (@D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.ambientHaar.{u_1} I inst H)))
  Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration.{u_1})

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.observation0.{u_1} : {I : Type u_1} →
  [inst : Fintype.{u_1} I] →
    (Hn :
        Nat →
          @ClosedSubgroup.{u_1} (I → Circle)
            (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
              @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)) →
      (H :
          @ClosedSubgroup.{u_1} (I → Circle)
            (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
              @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
            (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle)) →
        (h :
            @Filter.Tendsto.{0, 0} Nat Real
              (fun (n : Nat) =>
                @Metric.hausdorffDist.{u_1} (I → Circle)
                  (@pseudoMetricSpacePi.{u_1, 0} I (fun (a : I) => Circle) inst fun (b : I) =>
                    @MetricSpace.toPseudoMetricSpace.{0} Circle Circle.instMetricSpace)
                  (@SetLike.coe.{u_1, u_1}
                    (@ClosedSubgroup.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                      (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) =>
                        instTopologicalSpaceCircle))
                    (I → Circle)
                    (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                      (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) =>
                        instTopologicalSpaceCircle))
                    (Hn n))
                  (@SetLike.coe.{u_1, u_1}
                    (@ClosedSubgroup.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                      (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) =>
                        instTopologicalSpaceCircle))
                    (I → Circle)
                    (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                      (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                        @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                      (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) =>
                        instTopologicalSpaceCircle))
                    H))
              (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@nhds.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
            Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.signature.{u_1} PUnit.unit.{1} I :=
  fun {I : Type u_1} [Fintype.{u_1} I]
    (Hn :
      Nat →
        @ClosedSubgroup.{u_1} (I → Circle)
          (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
            @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
          (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
    (H :
      @ClosedSubgroup.{u_1} (I → Circle)
        (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) => @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
        (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
    (h :
      @Filter.Tendsto.{0, 0} Nat Real
        (fun (n : Nat) =>
          @Metric.hausdorffDist.{u_1} (I → Circle)
            (@pseudoMetricSpacePi.{u_1, 0} I (fun (a : I) => Circle) inst fun (b : I) =>
              @MetricSpace.toPseudoMetricSpace.{0} Circle Circle.instMetricSpace)
            (@SetLike.coe.{u_1, u_1}
              (@ClosedSubgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (I → Circle)
              (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (Hn n))
            (@SetLike.coe.{u_1, u_1}
              (@ClosedSubgroup.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              (I → Circle)
              (@ClosedSubgroup.instSetLike.{u_1} (I → Circle)
                (@Pi.group.{u_1, 0} I (fun (a : I) => Circle) fun (i : I) =>
                  @CommGroup.toGroup.{0} Circle Circle.instCommGroup)
                (@Pi.topologicalSpace.{0, u_1} I (fun (a : I) => Circle) fun (i : I) => instTopologicalSpaceCircle))
              H))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.signature.{u_1}
    Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.actual.{u_1} PUnit.unit.{1} I H

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result, part := .type, path := [.body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration.{u_1}).actual (Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration.{u_1}).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration.{u_1}).variation.1 (Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"TorusSubgroupHaarContinuity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity, declaration := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
