import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.QubitChordChannels
import Reg.Support.DependentFamily

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open _root_.D5.S3.Quantum.Information.ActualQubitChordObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.QubitChordChannels LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, v, b, hv, _, _, _, _, hvker, _⟩ :=
    (h (1/2) (by norm_num) (by norm_num) processor curve curve_density
      (fun u _ k => processor_exact u k)).1.2
  change v ∈ ((jointObservation processor).comp projectX).kerᗮ at hvker
  rw [erased_observation] at hvker
  exact hv (inner_self_eq_zero.mp
    (Submodule.inner_right_of_mem_orthogonal (by simp) hvker))

theorem variation_proof : Variation arena actual := ⟨actual_two_probe_chord_and_qfi, rejected, rejected_law⟩

theorem sensitivity_proof : Sensitivity arena actual :=
  sole_role_sensitivity arena.Law actual rejected (funext fun e => Empty.elim e) rejected_law

theorem dependence_proof : ObservationalDependence signature actual := by
    intro i
    exact ⟨(), processor, discardProcessor, observations_differ⟩

-- The source assessor reconstructs the original ConstantInfo.type from this
-- complete law and kernel-checks the bridge against that original statement.
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := variation_proof
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ G => jointObservation G) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "ActualQubitChordObstruction") "actual_two_probe_chord_and_qfi") "Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction/D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ G => jointObservation G) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.observationFact0, `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction


noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.arena
noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.arena
noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.arena) (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration).actual

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"actual_two_probe_chord_and_qfi\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.observation0 : (a : Real) →
  (_ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a) →
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (G :
          @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{0, 0}
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (fun
                (a b :
                  Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
              @instDecidableEqProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
        (rho :
            Real →
              Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) →
          (hrho :
              ∀ (u : Real),
                @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                    (@Set.Ioo.{0} Real Real.instPreorder
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          a)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    u →
                  And
                    (@Matrix.PosSemidef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      Complex Complex.instRing Complex.partialOrder Complex.instStarRing (rho u))
                    (@Eq.{1} Complex
                      (@Matrix.trace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        Complex.instAddCommMonoid (rho u))
                      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))) →
            (hexact :
                ∀ (u : Real),
                  @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                      (@Set.Ioo.{0} Real Real.instPreorder
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            a)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      u →
                    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
                      @Eq.{1}
                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                        (@DFunLike.coe.{1, 1, 1}
                          (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                            (@Matrix.addCommMonoid.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                              Complex.instAddCommMonoid)
                            (@Matrix.addCommMonoid.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex
                              Complex.instAddCommMonoid)
                            (@Matrix.module.{0, 0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Complex
                              Real.semiring Complex.instAddCommMonoid
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
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex)))
                            (@Matrix.module.{0, 0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Complex
                              Real.semiring Complex.instAddCommMonoid
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
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))))
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                          (fun
                              (x :
                                Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) =>
                            Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                          (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                            Real.semiring Real.semiring
                            (@Matrix.addCommMonoid.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                              Complex.instAddCommMonoid)
                            (@Matrix.addCommMonoid.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex
                              Complex.instAddCommMonoid)
                            (@Matrix.module.{0, 0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Complex
                              Real.semiring Complex.instAddCommMonoid
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
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex)))
                            (@Matrix.module.{0, 0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Complex
                              Real.semiring Complex.instAddCommMonoid
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
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex)))
                            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                          (D5.S3.Quantum.Information.ActualQubitChordObstruction.programOutput G k) (rho u))
                        (D5.S3.Quantum.Information.ActualQubitChordObstruction.probeTarget a u k)) →
              (c v : EuclideanSpace.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
                (b : Real) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (a : Real)
    (_ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (G :
      @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{0, 0}
        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (fun
            (a b :
              Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
          @instDecidableEqProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (rho :
      Real →
        Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
    (hrho :
      ∀ (u : Real),
        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
            (@Set.Ioo.{0} Real Real.instPreorder
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  a)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            u →
          And
            (@Matrix.PosSemidef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              Complex.instRing Complex.partialOrder Complex.instStarRing (rho u))
            (@Eq.{1} Complex
              (@Matrix.trace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex.instAddCommMonoid
                (rho u))
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))
    (hexact :
      ∀ (u : Real),
        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
            (@Set.Ioo.{0} Real Real.instPreorder
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  a)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            u →
          ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
            @Eq.{1}
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
              (@DFunLike.coe.{1, 1, 1}
                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                  (@Matrix.addCommMonoid.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    Complex.instAddCommMonoid)
                  (@Matrix.addCommMonoid.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex
                    Complex.instAddCommMonoid)
                  (@Matrix.module.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Complex Real.semiring
                    Complex.instAddCommMonoid
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
                        instInnerProductSpaceRealComplex)))
                  (@Matrix.module.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Complex Real.semiring
                    Complex.instAddCommMonoid
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
                        instInnerProductSpaceRealComplex))))
                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (fun
                    (x :
                      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) =>
                  Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
                  Real.semiring Real.semiring
                  (@Matrix.addCommMonoid.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    Complex.instAddCommMonoid)
                  (@Matrix.addCommMonoid.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex
                    Complex.instAddCommMonoid)
                  (@Matrix.module.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Complex Real.semiring
                    Complex.instAddCommMonoid
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
                        instInnerProductSpaceRealComplex)))
                  (@Matrix.module.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Complex Real.semiring
                    Complex.instAddCommMonoid
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
                        instInnerProductSpaceRealComplex)))
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                (D5.S3.Quantum.Information.ActualQubitChordObstruction.programOutput G k) (rho u))
              (D5.S3.Quantum.Information.ActualQubitChordObstruction.probeTarget a u k))
    (c v : EuclideanSpace.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) (b : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.signature
    D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.actual PUnit.unit.{1} PUnit.unit.{1} G

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"actual_two_probe_chord_and_qfi\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .function, .argument, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"actual_two_probe_chord_and_qfi\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration).actual (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration).variation.2.choose (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration).variation.1 (Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"ActualQubitChordObstruction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction, declaration := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
