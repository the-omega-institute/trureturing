import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FiniteDetectionTailBound
import Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionTailBound
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder Matrix MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound

universe u
namespace Survival

abbrev signature :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature

abbrev actual := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual

abbrev rejected := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1),
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
      (∀ m : ℕ, 0 ≤ R.readout () ⟨d, Q⟩ (m * d) - darkProjection Q L ∧
        R.readout () ⟨d, Q⟩ (m * d) - darkProjection Q L ≤
          (1 - g) ^ m • (1 - darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → darkProjection Q L * ρ = 0 →
          Summable (fun N : ℕ => (ρ * R.readout () ⟨d, Q⟩ N).trace.re) ∧
          ∑' N : ℕ, (ρ * R.readout () ⟨d, Q⟩ N).trace.re ≤ (d : ℝ) / g

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp
  exact finite_detection_tail_bound Q L hcomp

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by simp [Q]
  obtain ⟨g, _hg, _hg1, hblock, _htail⟩ := h Q L hcomp
  have hbad := (hblock 0).2
  simp only [rejected,
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected,
    realize, signature, Q, pow_zero, mul_one, one_smul] at hbad
  have hdiag := (Matrix.le_iff.mp hbad).diag_nonneg (i := 0)
  have hdiag' : (1 : ℂ) ≤ 0 := by simpa using hdiag
  exact (not_le_of_gt (zero_lt_one : (0 : ℂ) < 1)) hdiag'

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dependence_proof

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.finite_detection_tail_bound.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "FiniteDetectionTailBound") "finite_detection_tail_bound") "Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound/Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "arg", "arg", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound.finite_detection_tail_bound, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Survival
end Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound


noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
      Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.actual)
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"finite_detection_tail_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound.finite_detection_tail_bound, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.arena.{u_1}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.actual)
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.observation0.{u_1} : {d : Nat} →
  {ι : Type u_1} →
    [inst : Fintype.{u_1} ι] →
      (Q : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
        (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (hcomp :
              @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                      (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                    (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                      (@InvolutiveStar.toStar.{0} Complex
                        (@StarAddMonoid.toInvolutiveStar.{0} Complex
                          (@AddCommMonoid.toAddMonoid.{0} Complex
                            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                    Complex.instNonUnitalCommRing)))))
                          (@StarRing.toStarAddMonoid.{0} Complex
                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                  Complex.instNonUnitalCommRing)))
                            Complex.instStarRing)))
                      Q)
                    Q)
                  (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                    (@Finset.univ.{u_1} ι inst) fun (x : ι) =>
                    @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                        (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                      (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                        (@InvolutiveStar.toStar.{0} Complex
                          (@StarAddMonoid.toInvolutiveStar.{0} Complex
                            (@AddCommMonoid.toAddMonoid.{0} Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid.{0} Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                    Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                        (L x))
                      (L x)))
                (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
                  (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne)))) →
            (g : Real) →
              (ρ : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
                @Matrix.PosSemidef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing ρ →
                  @Eq.{1} Complex (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid ρ)
                      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
                    @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                            (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                          (@D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.darkProjection.{u_1} d ι Q L) ρ)
                        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                            (@Matrix.zero.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instZero))) →
                      (N : Nat) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                          Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature PUnit.unit.{1}
                          (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) :=
  fun {d : Nat} {ι : Type u_1} [Fintype.{u_1} ι] (Q : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hcomp :
      @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
          (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
              Complex.instMul Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
              (@InvolutiveStar.toStar.{0} Complex
                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                  (@AddCommMonoid.toAddMonoid.{0} Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              Q)
            Q)
          (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Finset.univ.{u_1} ι inst) fun (x : ι) =>
            @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
              (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                (@InvolutiveStar.toStar.{0} Complex
                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                    (@AddCommMonoid.toAddMonoid.{0} Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                              Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                (L x))
              (L x)))
        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
          (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne))))
    (g : Real) (ρ : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (a : @Matrix.PosSemidef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing ρ)
    (a_1 :
      @Eq.{1} Complex (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid ρ)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (a_2 :
      @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
            Complex.instMul Complex.instAddCommMonoid)
          (@D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.darkProjection.{u_1} d ι Q L) ρ)
        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.zero.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instZero))))
    (N : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) N

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"finite_detection_tail_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound.finite_detection_tail_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .body, .argument, .argument, .argument, .body, .body, .body, .body, .function, .argument, .function, .argument, .body, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"finite_detection_tail_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound.finite_detection_tail_bound, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration.{u_1}).actual (Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionTailBound\",\"Survival\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound.Survival.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
