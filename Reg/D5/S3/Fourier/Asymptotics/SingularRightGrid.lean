import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.SingularRightGrid
import Reg.Support.DependentFamily

open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ → ℂ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b =>
    |(∑ k ∈ Finset.range (Nat.floor (b/p.2.2)),
        (‖p.2.1 (((k:ℝ)+1)*p.2.2)‖^2-‖p.2.1 0‖^2) / ((k:ℝ)+1)) -
      ∫ x in 0..b, (‖p.2.1 x‖^2-‖p.2.1 0‖^2)/x|)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1:ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (A : ℝ), 0 < A → ∀ (f : ℝ → ℂ),
    AbsolutelyContinuousOnInterval f 0 A →
    IntervalIntegrable (fun x => ‖deriv f x‖^2) volume 0 A →
    ∀ (h b : ℝ), 0 < h → h ≤ b → b ≤ A →
    r.readout () ⟨A,f,h⟩ b ≤ 14*(1/Real.sqrt A+Real.sqrt A)*Real.sqrt h*
      (∫ x in 0..A, (‖f x‖^2+‖deriv f x‖^2))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0:ℂ)) 0 1 :=
    contDiffOn_const.absolutelyContinuousOnInterval
  have hi : IntervalIntegrable (fun x => ‖deriv (fun _ : ℝ => (0:ℂ)) x‖^2) volume 0 1 := by
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 1)
  have H := h 1 zero_lt_one (fun _ => 0) hc hi 1 1 zero_lt_one le_rfl le_rfl
  norm_num [rejected,realize] at H

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,(fun x : ℝ => (x:ℂ)),1⟩,0,1,?_⟩
  have he : (∫ x in (0:ℝ)..1, (‖(x:ℂ)‖^2-‖(0:ℂ)‖^2)/x) = 1/2 := by
    have heq : (fun x : ℝ => (‖(x:ℂ)‖^2-‖(0:ℂ)‖^2)/x) = fun x => x := by
      funext x
      simp only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
        Complex.norm_real,Real.norm_eq_abs,sq_abs]
      by_cases hx : x=0
      · simp [hx]
      · field_simp
    rw [heq,integral_id]
    norm_num
  simp only [actual,realize]
  have he' : (∫ x in (0:ℝ)..1, x^2/x) = 1/2 := by
    simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
      Complex.norm_real,Real.norm_eq_abs,sq_abs] using he
  norm_num [Finset.sum_range_succ,he']

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.SingularRightGrid.result,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (show j=i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.SingularRightGrid.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p b =>
    |(∑ k ∈ Finset.range (Nat.floor.{0} (b/p.2.2)),
        (‖p.2.1 (((k:ℝ)+1)*p.2.2)‖^2-‖p.2.1 0‖^2) / ((k:ℝ)+1)) -
      ∫ x in 0..b, (‖p.2.1 x‖^2-‖p.2.1 0‖^2)/x|) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "SingularRightGrid") "result") "Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid/Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p b =>
    |(∑ k ∈ Finset.range (Nat.floor.{0} (b/p.2.2)),
        (‖p.2.1 (((k:ℝ)+1)*p.2.2)‖^2-‖p.2.1 0‖^2) / ((k:ℝ)+1)) -
      ∫ x in 0..b, (‖p.2.1 x‖^2-‖p.2.1 0‖^2)/x|) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.SingularRightGrid, definition := none, coordinates := #[0, 2, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `D5.S3.Fourier.Asymptotics.SingularRightGrid.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid


noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.arena) (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration).actual

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `D5.S3.Fourier.Asymptotics.SingularRightGrid.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration).bridge

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.observation0 : (A : Real) →
  (hA : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A) →
    (f : Real → Complex) →
      (hf :
          @AbsolutelyContinuousOnInterval.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))
            f (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A) →
        (hf2 :
            @IntervalIntegrable.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@NormedAddGroup.toENormedAddMonoid.{0} Real
                (@NormedAddCommGroup.toNormedAddGroup.{0} Real Real.normedAddCommGroup))
              (fun (x : Real) =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@Norm.norm.{0} Complex Complex.instNorm
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Complex Complex.addCommGroup
                      (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                              (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                          instInnerProductSpaceRealComplex))
                      (@UniformSpace.toTopologicalSpace.{0} Complex
                        (@PseudoMetricSpace.toUniformSpace.{0} Complex
                          (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                            (@SeminormedCommRing.toSeminormedRing.{0} Complex
                              (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
                      f x))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A) →
          (h b : Real) →
            (hh :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  h) →
              (hhb : @LE.le.{0} Real Real.instLE h b) →
                (hbA : @LE.le.{0} Real Real.instLE b A) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.signature PUnit.unit.{1}
                    (@Sigma.mk.{0, 0} Real
                      (fun (x : Real) => @Sigma.{0, 0} (Real → Complex) fun (x : Real → Complex) => Real) A
                      (@Sigma.mk.{0, 0} (Real → Complex) (fun (x : Real → Complex) => Real) f h)) :=
  fun (A : Real)
    (hA : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A)
    (f : Real → Complex)
    (hf :
      @AbsolutelyContinuousOnInterval.{0} Complex
        (@SeminormedRing.toPseudoMetricSpace.{0} Complex
          (@SeminormedCommRing.toSeminormedRing.{0} Complex
            (@NormedCommRing.toSeminormedCommRing.{0} Complex
              (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))
        f (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A)
    (hf2 :
      @IntervalIntegrable.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@NormedAddGroup.toENormedAddMonoid.{0} Real
          (@NormedAddCommGroup.toNormedAddGroup.{0} Real Real.normedAddCommGroup))
        (fun (x : Real) =>
          @HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Norm.norm.{0} Complex Complex.instNorm
              (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                Complex Complex.addCommGroup
                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                    instInnerProductSpaceRealComplex))
                (@UniformSpace.toTopologicalSpace.{0} Complex
                  (@PseudoMetricSpace.toUniformSpace.{0} Complex
                    (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                      (@SeminormedCommRing.toSeminormedRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
                f x))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A)
    (h b : Real)
    (hh : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
    (hhb : @LE.le.{0} Real Real.instLE h b) (hbA : @LE.le.{0} Real Real.instLE b A) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.signature Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.actual
    PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} (Real → Complex) fun (x : Real → Complex) => Real) A
      (@Sigma.mk.{0, 0} (Real → Complex) (fun (x : Real → Complex) => Real) f h))
    b

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `D5.S3.Fourier.Asymptotics.SingularRightGrid.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `D5.S3.Fourier.Asymptotics.SingularRightGrid.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration).actual (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration).variation.1 (Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"SingularRightGrid\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid, declaration := `Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
