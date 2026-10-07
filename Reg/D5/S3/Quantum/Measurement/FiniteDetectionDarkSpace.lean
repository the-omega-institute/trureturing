import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
open LeanInformationAudit
open Lean Elab Command
open scoped BigOperators Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace

universe u

@[reducible] def darkSignature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℂ
  State p := Fin p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization darkSignature :=
  realize darkSignature
    (fun _ p ψ =>
      ((1 - (p.2ᴴ) ^ p.1 * p.2 ^ p.1).mulVec ψ : Fin p.1 → ℂ))
    (fun e => nomatch e)

def rejected : Realization darkSignature :=
  realize darkSignature
    (fun _ p _ => (0 : Fin p.1 → ℂ))
    (fun e => nomatch e)

def arena : Arena where
  signature := darkSignature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1)
    (ψ : Fin d → ℂ),
    (∀ n : ℕ, ∀ x : ι, (L x * Q ^ n).mulVec ψ = 0) ↔
      R.readout () ⟨d, Q⟩ ψ = 0



def oneVector : Fin 1 → ℂ := fun _ => 1

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have htest := h (d := 1) (ι := ULift.{u} Unit)
    (0 : Matrix (Fin 1) (Fin 1) ℂ)
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (by simp) oneVector
  have hall := htest.mpr (by rfl)
  have hzero := hall 0 ⟨()⟩
  have hentry := congrFun hzero 0
  have : (1 : ℂ) = 0 := by
    simpa [rejected, realize, darkSignature, oneVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_one] using hentry
  exact one_ne_zero this

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp ψ
  exact dark_space_eq_survival_defect_kernel Q L hcomp ψ

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

theorem dependence_proof : ObservationalDependence darkSignature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0⟩, oneVector, (0 : Fin 1 → ℂ), ?_⟩
  intro h
  have hentry := congrFun h 0
  norm_num [actual, realize, darkSignature, oneVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one] at hentry

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} darkSignature
    (fun _ p ψ =>
      ((1 - (p.2ᴴ) ^ p.1 * p.2 ^ p.1).mulVec ψ : Fin p.1 → ℂ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "FiniteDetectionDarkSpace") "dark_space_eq_survival_defect_kernel") "Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace/Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} darkSignature
    (fun _ p ψ =>
      ((1 - (p.2ᴴ) ^ p.1 * p.2 ^ p.1).mulVec ψ : Fin p.1 → ℂ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace


noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.arena.) (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"dark_space_eq_survival_defect_kernel\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.observation0.{u_1} : {d : Nat} →
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
            (ψ : Fin d → Complex) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.darkSignature PUnit.unit.{1}
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
    (ψ : Fin d → Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.darkSignature
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) ψ

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"dark_space_eq_survival_defect_kernel\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"dark_space_eq_survival_defect_kernel\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration.{u_1}).actual (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionDarkSpace\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
