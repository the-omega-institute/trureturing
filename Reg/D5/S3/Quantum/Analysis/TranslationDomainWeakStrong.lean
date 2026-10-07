import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
import Reg.Support.DependentFamily
open MeasureTheory Filter Set DomAddAct
open scoped ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
abbrev H := Lp ℂ 2 (volume : Measure ℝ)
abbrev signature : Signature where
  Params := ℝ
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ t u => DomAddAct.mk t +ᵥ u) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f h : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ))
      (hh : MemLp h 2 (volume : Measure ℝ)),
    (∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ → HasCompactSupport φ →
      (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * f x) = -∫ x : ℝ, (φ x : ℂ) * h x) ↔
    HasDerivAt (fun t : ℝ => R.readout () t (hf.toLp f)) (hh.toLp h) 0
-- An actual whole-family intervention changes the translation readout at every input.
def nonzeroVector : H :=
  indicatorConstLp (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    2 measurableSet_Icc (by simp) (1 : ℂ)
theorem nonzeroVector_ne : nonzeroVector ≠ 0 := by
  have hn : ‖nonzeroVector‖ = 1 := by
    rw [nonzeroVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [Measure.real, Real.volume_Icc]
  intro hz
  simpa [hz] using hn
def rejected : Realization signature :=
  realize signature (fun _ t _ => t • nonzeroVector) (fun e => nomatch e)
theorem actual_law : arena.Law actual := by
  intro f h hf hh
  exact translation_domain_iff f h hf hh
theorem rejected_law : ¬ arena.Law rejected := by
  intro hb
  have hz : MemLp (fun _ : ℝ => (0 : ℂ)) 2 (volume : Measure ℝ) := MemLp.zero'
  have hd := (hb (fun _ => 0) (fun _ => 0) hz hz).mp (by intro φ hc hs; simp)
  have hd' : HasDerivAt (fun t : ℝ => t • nonzeroVector) nonzeroVector 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const nonzeroVector
  have he := hd'.unique hd
  have hzero : hz.toLp (fun _ : ℝ => (0 : ℂ)) = 0 := hz.toLp_zero
  exact nonzeroVector_ne (by simpa [rejected, realize, hzero] using he)
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(0 : ℝ), (0 : H), nonzeroVector, ?_⟩
    intro he
    exact nonzeroVector_ne (by simpa [actual, realize] using he.symm)
def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
  coordinates := #[4]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "fn", "fn", "arg", "body"]
    stateOperand := some #["arg"] }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ t u => DomAddAct.mk.{0} t +ᵥ u) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Analysis") "TranslationDomainWeakStrong") "translation_domain_iff") "Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong/Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ t u => DomAddAct.mk.{0} t +ᵥ u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, definition := none, coordinates := #[4], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "fn", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.observationFact0, `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong


noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.arena
noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.arena
noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.arena) (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration).actual

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"translation_domain_iff\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.observation0 : (f h : Real → Complex) →
  (hf :
      @MeasureTheory.MemLp.{0, 0} Real Complex
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@ContinuousENorm.toENorm.{0} Complex
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedAddGroup.toPseudoMetricSpace.{0} Complex
                (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))))
          (@SeminormedAddGroup.toContinuousENorm.{0} Complex
            (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))))
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        f
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
    (hh :
        @MeasureTheory.MemLp.{0, 0} Real Complex
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@ContinuousENorm.toENorm.{0} Complex
            (@UniformSpace.toTopologicalSpace.{0} Complex
              (@PseudoMetricSpace.toUniformSpace.{0} Complex
                (@SeminormedAddGroup.toPseudoMetricSpace.{0} Complex
                  (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))))
            (@SeminormedAddGroup.toContinuousENorm.{0} Complex
              (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))))
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                (@SeminormedCommRing.toSeminormedRing.{0} Complex
                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
          h
          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
      (t : Real) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.signature PUnit.unit.{1} t :=
  fun (f h : Real → Complex)
    (hf :
      @MeasureTheory.MemLp.{0, 0} Real Complex
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@ContinuousENorm.toENorm.{0} Complex
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedAddGroup.toPseudoMetricSpace.{0} Complex
                (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))))
          (@SeminormedAddGroup.toContinuousENorm.{0} Complex
            (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))))
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        f
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hh :
      @MeasureTheory.MemLp.{0, 0} Real Complex
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@ContinuousENorm.toENorm.{0} Complex
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedAddGroup.toPseudoMetricSpace.{0} Complex
                (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))))
          (@SeminormedAddGroup.toContinuousENorm.{0} Complex
            (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Complex
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))))
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        h
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (t : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.signature
    Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.actual PUnit.unit.{1} t
    (@MeasureTheory.MemLp.toLp.{0, 0} Real Complex
      (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) Complex.instNormedAddCommGroup f hf)

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"translation_domain_iff\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"function\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff, part := .type, path := [.body, .body, .body, .body, .argument, .function, .function, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"translation_domain_iff\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration).actual (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration).variation.2.choose (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration).variation.1 (Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"TranslationDomainWeakStrong\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong, declaration := `Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
