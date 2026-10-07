import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
open LeanInformationAudit
open Lean Elab Command
open BigOperators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance

universe u

@[reducible] def branchSignature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization branchSignature :=
  realize branchSignature
    (fun _ p σ => traceNorm (p.2 - σ) / 2)
    (fun e => nomatch e)

def rejected : Realization branchSignature :=
  realize branchSignature
    (fun _ _ _ => (-1 : ℝ))
    (fun e => nomatch e)

def arena : Arena where
  signature := branchSignature
  Law R := ∀ {d : ℕ} {ι : Type*} [Fintype ι]
    (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (hρtrace : ρ.trace = 1)
    (hσ : σ.PosSemidef) (hσtrace : σ.trace = 1)
    (hB : (∑ i, (K i)ᴴ * K i) ≤ (1 : Matrix (Fin d) (Fin d) ℂ)),
    let B := ∑ i, (K i)ᴴ * K i
    let Φ := fun X : Matrix (Fin d) (Fin d) ℂ ↦ ∑ i, K i * X * (K i)ᴴ
    let p := (ρ * B).trace.re
    let q := (σ * B).trace.re
    let D := fun X Y : Matrix (Fin d) (Fin d) ℂ ↦ traceNorm (X - Y) / 2
    |p - q| ≤ R.readout () ⟨d, ρ⟩ σ ∧
      ((0 < p ∧ 0 < q) →
        max p q * D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ D ρ σ) ∧
      ∀ pStar ε : ℝ, 0 < pStar → pStar ≤ p → D ρ σ ≤ ε → ε < pStar →
        0 < q ∧ D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ ε / pStar



theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have htest := h (d := 1) (ι := ULift.{u} Empty)
    (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (fun i => nomatch i.down)
    Matrix.PosSemidef.one (by simp)
    Matrix.PosSemidef.one (by simp) (by simp)
  norm_num [rejected, realize, branchSignature] at htest

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ ρ σ K hρ hρtrace hσ hσtrace hB
  simpa only [actual, realize, branchSignature] using
    branch_conditioned_trace_distance ρ σ K hρ hρtrace hσ hσtrace hB

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

theorem dependence_proof : ObservationalDependence branchSignature actual := by
  intro i
  cases i
  refine ⟨⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ)⟩,
    (0 : Matrix (Fin 1) (Fin 1) ℂ), (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  have hnormZero : traceNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    simpa using h
  have hnormOne : traceNorm (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.PosSemidef.one :
        (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    simpa using h
  intro h
  norm_num [actual, realize, branchSignature, hnormZero, traceNorm_neg, hnormOne] at h

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} branchSignature
    (fun _ p σ => traceNorm.{0, 0, 0} (p.2 - σ) / 2)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "BranchConditionedTraceDistance") "branch_conditioned_trace_distance") "Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance/Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} branchSignature
    (fun _ p σ => traceNorm.{0, 0, 0} (p.2 - σ) / 2)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance


noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
      Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.actual)
    Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"branch_conditioned_trace_distance\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena.{u_1}
    Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.actual)
  Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.observation0.{u_1} : {d : Nat} →
  {ι : Type u_1} →
    [inst : Fintype.{u_1} ι] →
      (ρ σ : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
        (K : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (hρ :
              @Matrix.PosSemidef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing ρ) →
            (hρtrace :
                @Eq.{1} Complex (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid ρ)
                  (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
              (hσ :
                  @Matrix.PosSemidef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing
                    σ) →
                (hσtrace :
                    @Eq.{1} Complex (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid σ)
                      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                  (hB :
                      @LE.le.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                        (@Preorder.toLE.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (@Matrix.instPreOrder.{0, 0} Complex (Fin d) Complex.instRCLike))
                        (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                          (@Finset.univ.{u_1} ι inst) fun (i : ι) =>
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
                              (K i))
                            (K i))
                        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
                          (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                            (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero
                              Complex.instOne)))) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branchSignature PUnit.unit.{1}
                      (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d ρ) :=
  fun {d : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] (ρ σ : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (K : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hρ : @Matrix.PosSemidef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing ρ)
    (hρtrace :
      @Eq.{1} Complex (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid ρ)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (hσ : @Matrix.PosSemidef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing σ)
    (hσtrace :
      @Eq.{1} Complex (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid σ)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (hB :
      @LE.le.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@Preorder.toLE.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@Matrix.instPreOrder.{0, 0} Complex (Fin d) Complex.instRCLike))
        (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
          (@Finset.univ.{u_1} ι inst) fun (i : ι) =>
          @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
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
              (K i))
            (K i))
        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
          (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne)))) =>
  have B : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex :=
    @Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
      (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid) (@Finset.univ.{u_1} ι inst)
      fun (i : ι) =>
      @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
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
          (K i))
        (K i);
  have Φ : (X : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex :=
    fun (X : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) =>
    @Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
      (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid) (@Finset.univ.{u_1} ι inst)
      fun (i : ι) =>
      @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
          Complex.instMul Complex.instAddCommMonoid)
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
            Complex.instMul Complex.instAddCommMonoid)
          (K i) X)
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
          (K i));
  have p : Real :=
    Complex.re
      (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
            Complex.instMul Complex.instAddCommMonoid)
          ρ B));
  have q : Real :=
    Complex.re
      (@Matrix.trace.{0, 0} (Fin d) Complex (Fin.fintype d) Complex.instAddCommMonoid
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
            Complex.instMul Complex.instAddCommMonoid)
          σ B));
  have D : (X Y : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) → Real :=
    fun (X Y : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm.{0, 0, 0} (Fin d) (Fin d) Complex (Fin.fintype d)
        (Fin.fintype d) Complex.instRCLike
        (@HSub.hSub.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@instHSub.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.sub.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instSub))
          X Y))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))));
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branchSignature
    Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d ρ) σ

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"branch_conditioned_trace_distance\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"branch_conditioned_trace_distance\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration.{u_1}).actual (Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"BranchConditionedTraceDistance\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance, declaration := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
