import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.FirstDomainWeakCCR
import Reg.Support.DependentFamily
open MeasureTheory Filter Set
open scoped ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.FirstDomainWeakCCR
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR
abbrev H := Lp ℂ 2 (volume : Measure ℝ)
abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ u v => inner ℂ u v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (hbar : ℝ) (hhbar : 0 < hbar)
    (f g df dg : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hdf : MemLp df 2 (volume : Measure ℝ)) (hdg : MemLp dg 2 (volume : Measure ℝ))
    (hxf : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 (volume : Measure ℝ))
    (hxg : MemLp (fun x : ℝ => (x : ℂ) * g x) 2 (volume : Measure ℝ))
    (hwf : ∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
      HasCompactSupport φ → (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * f x) =
      -∫ x : ℝ, (φ x : ℂ) * df x)
    (hwg : ∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
      HasCompactSupport φ → (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * g x) =
      -∫ x : ℝ, (φ x : ℂ) * dg x),
    R.readout (0 : Fin 3) () (hxf.toLp (fun x : ℝ => (x : ℂ) * f x))
        ((-Complex.I * (hbar : ℂ)) • hdg.toLp dg) -
      R.readout (1 : Fin 3) () ((-Complex.I * (hbar : ℂ)) • hdf.toLp df)
        (hxg.toLp (fun x : ℝ => (x : ℂ) * g x)) =
      Complex.I * (hbar : ℂ) * R.readout (2 : Fin 3) () (hf.toLp f) (hg.toLp g)

def nonzeroVector : H :=
  indicatorConstLp (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    2 measurableSet_Icc (by simp) (1 : ℂ)
theorem nonzeroVector_ne : nonzeroVector ≠ 0 := by
  have hn : ‖nonzeroVector‖ = 1 := by
    rw [nonzeroVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [Measure.real, Real.volume_Icc]
  intro hz
  simpa [hz] using hn

def rejected (i : Fin 3) : Realization signature :=
  realize signature (fun j _ u v => inner ℂ u v + if j = i then 1 else 0) (fun e => nomatch e)
theorem actual_law : arena.Law actual := by
  intro hbar hhbar f g df dg hf hg hdf hdg hxf hxg hwf hwg
  exact first_domain_weak_ccr hbar hhbar f g df dg hf hg hdf hdg hxf hxg hwf hwg

theorem rejected_law (i : Fin 3) : ¬ arena.Law (rejected i) := by
  intro hb
  have hz : MemLp (fun _ : ℝ => (0 : ℂ)) 2 (volume : Measure ℝ) := MemLp.zero'
  have hx : MemLp (fun x : ℝ => (x : ℂ) * (0 : ℂ)) 2 (volume : Measure ℝ) := by
    simpa using hz
  have hx0 : hx.toLp (fun x : ℝ => (x : ℂ) * (0 : ℂ)) = 0 := by
    apply Lp.ext
    filter_upwards [hx.coeFn_toLp] with x h
    simpa using h
  have hbad := hb 1 (by norm_num) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) hz hz hz hz hx hx
    (by intro φ hc hs; simp) (by intro φ hc hs; simp)
  have hzero : hz.toLp (fun _ : ℝ => (0 : ℂ)) = 0 := hz.toLp_zero
  simp only [rejected, realize, hx0, hzero, smul_zero, inner_zero_left,
    inner_zero_right, Complex.ofReal_one, mul_one, zero_add, sub_zero] at hbad
  fin_cases i <;> norm_num [Fin.ext_iff, Complex.ext_iff] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p u v
      simp [rejected, actual, realize, hj]
    · intro i
      nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : H), nonzeroVector, ?_⟩
    intro he
    have hz : inner ℂ nonzeroVector nonzeroVector = 0 := by
      simpa [actual, realize] using (congrFun he nonzeroVector).symm
    exact nonzeroVector_ne (inner_self_eq_zero.mp hz)

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR
  coordinates := #[]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"], functionOperand := true },
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn"], functionOperand := true },
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"], functionOperand := true }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ u v => inner.{0, 0} ℂ u v) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Analysis") "FirstDomainWeakCCR") "first_domain_weak_ccr") "Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR/Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ u v => inner.{0, 0} ℂ u v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observationFact0, `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observationFact1, `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observationFact2, `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR


noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.arena
noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.arena
noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.arena) (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration).actual

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"first_domain_weak_ccr\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) where
  values := [(fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
    (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
    (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observation0 : (hbar : Real) →
  (hhbar :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) hbar) →
    (f g df dg : Real → Complex) →
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
        (hg :
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
              g
              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
          (hdf :
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
                df
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
            (hdg :
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
                  dg
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
              (hxf :
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
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))))))
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
                    (fun (x : Real) =>
                      @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                        (Complex.ofReal x) (f x))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
                (hxg :
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
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))))))
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
                      (fun (x : Real) =>
                        @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                          (Complex.ofReal x) (g x))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
                  (hwf :
                      ∀ (φ : Real → Real),
                        @ContDiff.{0, 0, 0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                            Real.normedAddCommGroup
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                            Real Real.normedAddCommGroup
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
                          @HasCompactSupport.{0, 0} Real Real
                              (@UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              Real.instZero φ →
                            @Eq.{1} Complex
                              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)
                                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                  (Complex.ofReal
                                    (@deriv.{0, 0} Real
                                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                      Real Real.instAddCommGroup
                                      (@Semiring.toModule.{0} Real
                                        (@DivisionSemiring.toSemiring.{0} Real
                                          (@Semifield.toDivisionSemiring.{0} Real
                                            (@Field.toSemifield.{0} Real
                                              (@NormedField.toField.{0} Real
                                                (@NontriviallyNormedField.toNormedField.{0} Real
                                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                    Real.denselyNormedField)))))))
                                      (@UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                      φ x))
                                  (f x))
                              (@Neg.neg.{0} Complex Complex.instNeg
                                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)
                                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                    (Complex.ofReal (φ x)) (df x)))) →
                    (hwg :
                        ∀ (φ : Real → Real),
                          @ContDiff.{0, 0, 0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                              Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              Real Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
                            @HasCompactSupport.{0, 0} Real Real
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                Real.instZero φ →
                              @Eq.{1} Complex
                                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)
                                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                    (Complex.ofReal
                                      (@deriv.{0, 0} Real
                                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                        Real Real.instAddCommGroup
                                        (@Semiring.toModule.{0} Real
                                          (@DivisionSemiring.toSemiring.{0} Real
                                            (@Semifield.toDivisionSemiring.{0} Real
                                              (@Field.toSemifield.{0} Real
                                                (@NormedField.toField.{0} Real
                                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                      Real.denselyNormedField)))))))
                                        (@UniformSpace.toTopologicalSpace.{0} Real
                                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                        φ x))
                                    (g x))
                                (@Neg.neg.{0} Complex Complex.instNeg
                                  (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)
                                    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                    @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                      (Complex.ofReal (φ x)) (dg x)))) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature PUnit.unit.{1} →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature
                          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
                            (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
                              (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
                          PUnit.unit.{1} :=
  fun (hbar : Real)
    (hhbar :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) hbar)
    (f g df dg : Real → Complex)
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
    (hg :
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
        g
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hdf :
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
        df
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hdg :
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
        dg
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hxf :
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
        (fun (x : Real) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal x) (f x))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hxg :
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
        (fun (x : Real) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal x) (g x))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hwf :
      ∀ (φ : Real → Real),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
            Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
          @HasCompactSupport.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instZero φ →
            @Eq.{1} Complex
              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (Complex.ofReal
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Real Real.instAddCommGroup
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      φ x))
                  (f x))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (Complex.ofReal (φ x)) (df x))))
    (hwg :
      ∀ (φ : Real → Real),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
            Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
          @HasCompactSupport.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instZero φ →
            @Eq.{1} Complex
              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (Complex.ofReal
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Real Real.instAddCommGroup
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      φ x))
                  (g x))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (Complex.ofReal (φ x)) (dg x)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
    PUnit.unit.{1}

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"first_domain_weak_ccr\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .function, .function], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observation1 : (hbar : Real) →
  (hhbar :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) hbar) →
    (f g df dg : Real → Complex) →
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
        (hg :
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
              g
              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
          (hdf :
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
                df
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
            (hdg :
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
                  dg
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
              (hxf :
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
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))))))
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
                    (fun (x : Real) =>
                      @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                        (Complex.ofReal x) (f x))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
                (hxg :
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
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))))))
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
                      (fun (x : Real) =>
                        @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                          (Complex.ofReal x) (g x))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
                  (hwf :
                      ∀ (φ : Real → Real),
                        @ContDiff.{0, 0, 0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                            Real.normedAddCommGroup
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                            Real Real.normedAddCommGroup
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
                          @HasCompactSupport.{0, 0} Real Real
                              (@UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              Real.instZero φ →
                            @Eq.{1} Complex
                              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)
                                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                  (Complex.ofReal
                                    (@deriv.{0, 0} Real
                                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                      Real Real.instAddCommGroup
                                      (@Semiring.toModule.{0} Real
                                        (@DivisionSemiring.toSemiring.{0} Real
                                          (@Semifield.toDivisionSemiring.{0} Real
                                            (@Field.toSemifield.{0} Real
                                              (@NormedField.toField.{0} Real
                                                (@NontriviallyNormedField.toNormedField.{0} Real
                                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                    Real.denselyNormedField)))))))
                                      (@UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                      φ x))
                                  (f x))
                              (@Neg.neg.{0} Complex Complex.instNeg
                                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)
                                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                    (Complex.ofReal (φ x)) (df x)))) →
                    (hwg :
                        ∀ (φ : Real → Real),
                          @ContDiff.{0, 0, 0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                              Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              Real Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
                            @HasCompactSupport.{0, 0} Real Real
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                Real.instZero φ →
                              @Eq.{1} Complex
                                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)
                                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                    (Complex.ofReal
                                      (@deriv.{0, 0} Real
                                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                        Real Real.instAddCommGroup
                                        (@Semiring.toModule.{0} Real
                                          (@DivisionSemiring.toSemiring.{0} Real
                                            (@Semifield.toDivisionSemiring.{0} Real
                                              (@Field.toSemifield.{0} Real
                                                (@NormedField.toField.{0} Real
                                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                      Real.denselyNormedField)))))))
                                        (@UniformSpace.toTopologicalSpace.{0} Real
                                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                        φ x))
                                    (g x))
                                (@Neg.neg.{0} Complex Complex.instNeg
                                  (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)
                                    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                    @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                      (Complex.ofReal (φ x)) (dg x)))) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature PUnit.unit.{1} →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature
                          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
                            (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
                              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                          PUnit.unit.{1} :=
  fun (hbar : Real)
    (hhbar :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) hbar)
    (f g df dg : Real → Complex)
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
    (hg :
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
        g
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hdf :
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
        df
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hdg :
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
        dg
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hxf :
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
        (fun (x : Real) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal x) (f x))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hxg :
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
        (fun (x : Real) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal x) (g x))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hwf :
      ∀ (φ : Real → Real),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
            Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
          @HasCompactSupport.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instZero φ →
            @Eq.{1} Complex
              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (Complex.ofReal
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Real Real.instAddCommGroup
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      φ x))
                  (f x))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (Complex.ofReal (φ x)) (df x))))
    (hwg :
      ∀ (φ : Real → Real),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
            Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
          @HasCompactSupport.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instZero φ →
            @Eq.{1} Complex
              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (Complex.ofReal
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Real Real.instAddCommGroup
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      φ x))
                  (g x))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (Complex.ofReal (φ x)) (dg x)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
        (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    PUnit.unit.{1}

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"first_domain_weak_ccr\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"function\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument, .function, .function], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observation2 : (hbar : Real) →
  (hhbar :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) hbar) →
    (f g df dg : Real → Complex) →
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
        (hg :
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
              g
              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
          (hdf :
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
                df
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
            (hdg :
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
                  dg
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
              (hxf :
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
                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                        instCommCStarAlgebraComplex)))))))))
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
                    (fun (x : Real) =>
                      @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                        (Complex.ofReal x) (f x))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
                (hxg :
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
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                          instCommCStarAlgebraComplex)))))))))
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
                      (fun (x : Real) =>
                        @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                          (Complex.ofReal x) (g x))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) →
                  (hwf :
                      ∀ (φ : Real → Real),
                        @ContDiff.{0, 0, 0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                            Real.normedAddCommGroup
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                            Real Real.normedAddCommGroup
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
                          @HasCompactSupport.{0, 0} Real Real
                              (@UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              Real.instZero φ →
                            @Eq.{1} Complex
                              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                    Complex.instNormedAddCommGroup)
                                  instInnerProductSpaceRealComplex)
                                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                  (Complex.ofReal
                                    (@deriv.{0, 0} Real
                                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                      Real Real.instAddCommGroup
                                      (@Semiring.toModule.{0} Real
                                        (@DivisionSemiring.toSemiring.{0} Real
                                          (@Semifield.toDivisionSemiring.{0} Real
                                            (@Field.toSemifield.{0} Real
                                              (@NormedField.toField.{0} Real
                                                (@NontriviallyNormedField.toNormedField.{0} Real
                                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                    Real.denselyNormedField)))))))
                                      (@UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                      φ x))
                                  (f x))
                              (@Neg.neg.{0} Complex Complex.instNeg
                                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)
                                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                    (Complex.ofReal (φ x)) (df x)))) →
                    (hwg :
                        ∀ (φ : Real → Real),
                          @ContDiff.{0, 0, 0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                              Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              Real Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
                            @HasCompactSupport.{0, 0} Real Real
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                Real.instZero φ →
                              @Eq.{1} Complex
                                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                      Complex.instNormedAddCommGroup)
                                    instInnerProductSpaceRealComplex)
                                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                    (Complex.ofReal
                                      (@deriv.{0, 0} Real
                                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                        Real Real.instAddCommGroup
                                        (@Semiring.toModule.{0} Real
                                          (@DivisionSemiring.toSemiring.{0} Real
                                            (@Semifield.toDivisionSemiring.{0} Real
                                              (@Field.toSemifield.{0} Real
                                                (@NormedField.toField.{0} Real
                                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                      Real.denselyNormedField)))))))
                                        (@UniformSpace.toTopologicalSpace.{0} Real
                                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                        φ x))
                                    (g x))
                                (@Neg.neg.{0} Complex Complex.instNeg
                                  (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                        Complex.instNormedAddCommGroup)
                                      instInnerProductSpaceRealComplex)
                                    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                                    @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                                      (Complex.ofReal (φ x)) (dg x)))) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature PUnit.unit.{1} →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature
                          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
                            (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
                              (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          PUnit.unit.{1} :=
  fun (hbar : Real)
    (hhbar :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) hbar)
    (f g df dg : Real → Complex)
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
    (hg :
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
        g
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hdf :
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
        df
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hdg :
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
        dg
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hxf :
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
        (fun (x : Real) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal x) (f x))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hxg :
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
        (fun (x : Real) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal x) (g x))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (hwf :
      ∀ (φ : Real → Real),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
            Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
          @HasCompactSupport.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instZero φ →
            @Eq.{1} Complex
              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (Complex.ofReal
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Real Real.instAddCommGroup
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      φ x))
                  (f x))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (Complex.ofReal (φ x)) (df x))))
    (hwg :
      ∀ (φ : Real → Real),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
            Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@WithTop.some.{0} ENat (@Top.top.{0} ENat instTopENat)) φ →
          @HasCompactSupport.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instZero φ →
            @Eq.{1} Complex
              (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (Complex.ofReal
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      Real Real.instAddCommGroup
                      (@Semiring.toModule.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      φ x))
                  (g x))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@MeasureTheory.integral.{0, 0} Real Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) fun (x : Real) =>
                  @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (Complex.ofReal (φ x)) (dg x)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.signature Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    PUnit.unit.{1}

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observationFact2 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"first_domain_weak_ccr\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"observation2\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .function], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.observation2, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"first_domain_weak_ccr\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR.first_domain_weak_ccr, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration).actual (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration).variation.2.choose (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration).variation.1 (Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Analysis\",\"FirstDomainWeakCCR\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR, declaration := `Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
