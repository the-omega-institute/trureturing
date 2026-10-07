import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.EventualClickDoobInstrument
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Measurement.EventualClickDoobInstrument
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open Filter LeanInformationAudit Matrix Topology
open Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument

@[reducible] def effectSignature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization effectSignature :=
  realize effectSignature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization effectSignature :=
  realize effectSignature (fun _ _ F => F + 1) (fun e => nomatch e)

def arena : Arena where
  signature := effectSignature
  Law S := ∀ {d : ℕ} {α ξ β : Type}
    [Fintype α] [Fintype ξ] [Fintype β]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ξ → β → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ x, ∑ b, (L x b)ᴴ * L x b = 1)
    (F : Matrix (Fin d) (Fin d) ℂ)
    (_hF : Tendsto (survival Q) atTop (𝓝 F)),
    let N := PhyslibLeaf.MatrixMap.of_kraus Q Q
    let C := fun x => PhyslibLeaf.MatrixMap.of_kraus (L x) (L x)
    let R := 1 - S.readout () d F
    let P := spectralSupport R
    let G := cfc (fun t : ℝ => Real.sqrt t) R
    let Gplus := spectralInverseSqrt R
    let Ntilde := fun X => G * N (Gplus * X * Gplus) * G
    let Ctilde := fun x X => C x (Gplus * X * Gplus)
    R = noClickDual Q R + ∑ x, noClickDual (L x) 1 ∧
    (∀ a, P * Q a * (1 - P) = 0) ∧
    (∀ x b, L x b * (1 - P) = 0) ∧
    (∀ H, H = P * H * P → noClickDual Q H = P * noClickDual Q H * P) ∧
    (∀ x Z, noClickDual (L x) Z = P * noClickDual (L x) Z * P) ∧
    Gplus * G = P ∧ G * Gplus = P ∧ P * G = G ∧
    (∀ X, Ntilde X =
      ∑ a, (G * Q a * Gplus) * X * (G * Q a * Gplus)ᴴ) ∧
    (∀ x X, Ctilde x X =
      ∑ b, (L x b * Gplus) * X * (L x b * Gplus)ᴴ) ∧
    (∑ a, (G * Q a * Gplus)ᴴ * P * (G * Q a * Gplus) +
      ∑ x, ∑ b, (L x b * Gplus)ᴴ * (L x b * Gplus) = P) ∧
    (∀ X, Ntilde (G * X * G) = G * N X * G) ∧
    (∀ x X, Ctilde x (G * X * G) = C x X) ∧
    ∀ (rho : DensityState (Fin d)) (n : ℕ), 1 ≤ n →
      let rhoMatrix : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm rho.1
      let r := (rhoMatrix * R).trace.re
      0 < r → ∀ x,
        let original := C x ((N^[n - 1]) rhoMatrix)
        let conditioned := Ctilde x ((Ntilde^[n - 1])
          (((r : ℂ)⁻¹) • (G * rhoMatrix * G)))
        conditioned = ((r : ℂ)⁻¹) • original ∧
        conditioned.trace = original.trace / (r : ℂ) ∧
        (original.trace ≠ 0 → conditioned.trace ≠ 0 ∧
          (conditioned.trace)⁻¹ • conditioned = (original.trace)⁻¹ • original)



theorem actual_law : arena.Law actual := by
  intro d α ξ β _ _ _ Q L hcomp F hF
  simpa only [actual, realize, effectSignature] using
    eventual_click_doob_instrument Q L hcomp F hF

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let Q : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0
  let L : Unit → Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 1
  have hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ x, ∑ b, (L x b)ᴴ * L x b = 1 := by
    simp [Q, L]
  have hF : Tendsto (survival Q) atTop
      (𝓝 (0 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    cases n with
    | zero => omega
    | succ n => simp [survival, noClickDual, Q]
  have hbad := (h Q L hcomp 0 hF).1
  have hentry := congrFun (congrFun hbad 0) 0
  norm_num [rejected, realize, effectSignature, noClickDual] at hentry

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

theorem dependence_proof : ObservationalDependence effectSignature actual := by
  intro i
  cases i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ),
    (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num [actual, realize, effectSignature] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.eventual_click_doob_instrument) (type_of% (realize.{0, 0, 0, 0, 0} effectSignature (fun _ _ F => F) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "EventualClickDoobInstrument") "eventual_click_doob_instrument") "Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument/Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} effectSignature (fun _ _ F => F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument.eventual_click_doob_instrument, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument


noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
      Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.actual)
    Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"eventual_click_doob_instrument\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument.eventual_click_doob_instrument, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena
    Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.actual)
  Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.observation0 : {d : Nat} →
  {α ξ β : Type} →
    [inst : Fintype.{0} α] →
      [inst_1 : Fintype.{0} ξ] →
        [inst_2 : Fintype.{0} β] →
          (Q : α → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
            (L : ξ → β → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
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
                      (@Finset.sum.{0, 0} ξ (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                        (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                        (@Finset.univ.{0} ξ inst_1) fun (x : ξ) =>
                        @Finset.sum.{0, 0} β (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                          (@Finset.univ.{0} β inst_2) fun (b : β) =>
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
                              (L x b))
                            (L x b)))
                    (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
                      (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                        (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero
                          Complex.instOne)))) →
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
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.effectSignature PUnit.unit.{1} d :=
  fun {d : Nat} {α ξ β : Type} [inst : Fintype.{0} α] [Fintype.{0} ξ] [inst_2 : Fintype.{0} β]
    (Q : α → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (L : ξ → β → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
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
          (@Finset.sum.{0, 0} ξ (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Finset.univ.{0} ξ inst_1) fun (x : ξ) =>
            @Finset.sum.{0, 0} β (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
              (@Finset.univ.{0} β inst_2) fun (b : β) =>
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
                  (L x b))
                (L x b)))
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
          F)) =>
  have N :
    @D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.{0, 0, 0} (Fin d) (Fin d) Complex
      (@CommSemiring.toSemiring.{0} Complex Complex.instCommSemiring) :=
    @D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus.{0, 0, 0, 0} (Fin d) (Fin d) Complex
      (Fin.fintype d)
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
      Complex.instCommSemiring α inst Q Q;
  have C :
    (x : ξ) →
      @D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.{0, 0, 0} (Fin d) (Fin d) Complex
        (@CommSemiring.toSemiring.{0} Complex Complex.instCommSemiring) :=
    fun (x : ξ) =>
    @D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus.{0, 0, 0, 0} (Fin d) (Fin d) Complex
      (Fin.fintype d)
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
      Complex.instCommSemiring β inst_2 (L x) (L x);
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.effectSignature
    Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.actual PUnit.unit.{1} d F

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"eventual_click_doob_instrument\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letValue\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument.eventual_click_doob_instrument, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letValue, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"eventual_click_doob_instrument\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument.eventual_click_doob_instrument, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration).actual (Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"EventualClickDoobInstrument\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument, declaration := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
