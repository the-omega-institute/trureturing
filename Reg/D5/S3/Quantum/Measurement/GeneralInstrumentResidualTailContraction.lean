import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
open Lean Elab Command
open Filter LeanInformationAudit Matrix Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction

@[reducible] def residualSignature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization residualSignature :=
  realize residualSignature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization residualSignature :=
  realize residualSignature (fun _ _ F => F + 1) (fun e => nomatch e)

def arena : Arena where
  signature := residualSignature
  Law R := ∀ {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (_hF : Tendsto (survival Q) atTop (𝓝 F)),
    (∀ n, survival Q n - R.readout () d F =
        (noClickDual Q)^[n] ((1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
      0 ≤ survival Q n - F ∧
        survival Q n - F ≤ (1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
    (∃ M : ℕ, 1 ≤ M ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      survival Q M - F ≤ q • ((1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
      (∀ n, survival Q n - F ≤
        q ^ (n / M) • ((1 : Matrix (Fin d) (Fin d) ℂ) - F)) ∧
      Summable (fun n => survival Q n - F) ∧
      let T := ∑' n, (survival Q n - F)
      0 ≤ T ∧ T ≤ ((M : ℝ) / (1 - q)) •
          ((1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
        T - noClickDual Q T = (1 : Matrix (Fin d) (Fin d) ℂ) - F ∧
        (∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          let rρ := (ρ * ((1 : Matrix (Fin d) (Fin d) ℂ) - F)).trace.re
          0 < rρ → (ρ * T).trace.re / rρ ≤ (M : ℝ) / (1 - q)) ∧
        (∀ k, 0 ≤ T - ∑ n ∈ Finset.range (k * M), (survival Q n - F) ∧
          T - ∑ n ∈ Finset.range (k * M), (survival Q n - F) ≤
            ((M : ℝ) * q ^ k / (1 - q)) •
              ((1 : Matrix (Fin d) (Fin d) ℂ) - F)) ∧
        (∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          let rρ := (ρ * ((1 : Matrix (Fin d) (Fin d) ℂ) - F)).trace.re
          0 < rρ → ∀ k,
            0 ≤ (ρ * (T - ∑ n ∈ Finset.range (k * M),
              (survival Q n - F))).trace.re / rρ ∧
            (ρ * (T - ∑ n ∈ Finset.range (k * M),
              (survival Q n - F))).trace.re / rρ ≤
                (M : ℝ) * q ^ k / (1 - q)) ∧
        ∀ (X : Matrix (Fin d) (Fin d) ℂ) (c : ℝ),
          X - noClickDual Q X = (1 : Matrix (Fin d) (Fin d) ℂ) - F →
            0 ≤ X → X ≤ c • ((1 : Matrix (Fin d) (Fin d) ℂ) - F) → X = T)



theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp F hF
  simpa only [actual, realize, residualSignature] using
    residual_tail_contraction Q L hcomp F hF

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let Q : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0
  let L : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
  have hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1 := by
    simp [Q, L]
  have hF : Tendsto (survival Q) atTop
      (𝓝 (0 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    cases n with
    | zero => omega
    | succ n => simp [survival, noClickDual, Q]
  have hbad := (h Q L hcomp 0 hF).1 0 |>.1
  have hentry := congrFun (congrFun hbad 0) 0
  norm_num [rejected, realize, residualSignature, survival] at hentry

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence residualSignature actual := by
  intro i
  cases i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ), (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num [actual, realize, residualSignature] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residual_tail_contraction) (type_of% (realize.{0, 0, 0, 0, 0} residualSignature (fun _ _ F => F) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "GeneralInstrumentResidualTailContraction") "residual_tail_contraction") "Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction/Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} residualSignature (fun _ _ F => F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residual_tail_contraction, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction


noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
      Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.actual)
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"residual_tail_contraction\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residual_tail_contraction, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.arena
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.actual)
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.observation0 : {d : Nat} →
  {α ι : Type} →
    [inst : Fintype.{0} α] →
      [inst_1 : Fintype.{0} ι] →
        (Q : α → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
            (hcomp :
                @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
                    (@Finset.sum.{0, 0} α (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                      (@Finset.univ.{0} α inst) fun (a : α) =>
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
                          (Q a))
                        (Q a))
                    (@Finset.sum.{0, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                      (@Finset.univ.{0} ι inst_1) fun (i : ι) =>
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
                          (L i))
                        (L i)))
                  (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
                    (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne)))) →
              (F : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
                (hF :
                    @Filter.Tendsto.{0, 0} Nat (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival d α inst Q)
                      (@Filter.atTop.{0} Nat Nat.instPreorder)
                      (@nhds.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                        (@instTopologicalSpaceMatrix.{0, 0, 0} (Fin d) (Fin d) Complex
                          (@UniformSpace.toTopologicalSpace.{0} Complex
                            (@PseudoMetricSpace.toUniformSpace.{0} Complex
                              (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                                (@SeminormedCommRing.toSeminormedRing.{0} Complex
                                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))
                        F)) →
                  (n : Nat) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residualSignature
                      PUnit.unit.{1} d :=
  fun {d : Nat} {α ι : Type} [Fintype.{0} α] [Fintype.{0} ι] (Q : α → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hcomp :
      @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
          (@Finset.sum.{0, 0} α (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Finset.univ.{0} α inst) fun (a : α) =>
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
                (Q a))
              (Q a))
          (@Finset.sum.{0, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Finset.univ.{0} ι inst_1) fun (i : ι) =>
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
                (L i))
              (L i)))
        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
          (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne))))
    (F : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hF :
      @Filter.Tendsto.{0, 0} Nat (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival d α inst Q)
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@instTopologicalSpaceMatrix.{0, 0, 0} (Fin d) (Fin d) Complex
            (@UniformSpace.toTopologicalSpace.{0} Complex
              (@PseudoMetricSpace.toUniformSpace.{0} Complex
                (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                  (@SeminormedCommRing.toSeminormedRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))))
          F))
    (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residualSignature
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.actual PUnit.unit.{1} d F

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"residual_tail_contraction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residual_tail_contraction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"residual_tail_contraction\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.residual_tail_contraction, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration).actual (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentResidualTailContraction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
