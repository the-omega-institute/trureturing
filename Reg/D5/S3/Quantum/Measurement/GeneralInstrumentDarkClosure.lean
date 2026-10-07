import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
import Reg.Support.DependentFamily
import Reg.Support.GeneralInstrumentModels

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open Reg.Support.GeneralInstrumentModels
open LeanInformationAudit Matrix Filter Topology
open scoped ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d X => (1 : Matrix (Fin d) (Fin d) ℂ) - X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (Q : α → Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1),
    (∀ n, darkLayer Q L n = LinearMap.ker (R.readout () d (survival Q n)).mulVecLin) ∧
      (∀ n, d ≤ n → darkLayer Q L n = darkLayer Q L d) ∧
      (∀ i, ∀ v ∈ darkLayer Q L d, (L i).mulVec v = 0) ∧
      (∀ a, ∀ v ∈ darkLayer Q L d, (Q a).mulVec v ∈ darkLayer Q L d) ∧
      ∀ V : Submodule ℂ (Fin d → ℂ), (∀ i, ∀ v ∈ V, (L i).mulVec v = 0) →
        (∀ a, ∀ v ∈ V, (Q a).mulVec v ∈ V) → V ≤ darkLayer Q L d

theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp
  exact darkLayer_closure Q L hcomp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (d := 1) (α := Unit) (ι := Unit)
    (fun _ => 0) (fun _ => 1) (complete 1)).1 1
  have he : (⊥ : Submodule ℂ (Fin 1 → ℂ)) = ⊤ := by
    simpa [rejected, realize, dark_layer_one, Matrix.mulVecLin_zero] using hb
  exact bot_ne_top he

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

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [actual, realize] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.darkLayer_closure) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ d X => (1 : Matrix.{0, 0, 0} (Fin d) (Fin d) ℂ) - X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "GeneralInstrumentDarkClosure") "darkLayer_closure") "Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure/Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ d X => (1 : Matrix.{0, 0, 0} (Fin d) (Fin d) ℂ) - X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.darkLayer_closure, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure


noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.arena) (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration).actual

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"darkLayer_closure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.darkLayer_closure, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.observation0 : {d : Nat} →
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
              (n : Nat) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.signature PUnit.unit.{1} d :=
  fun {d : Nat} {α ι : Type} [inst : Fintype.{0} α] [Fintype.{0} ι] (Q : α → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
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
    (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.signature
    Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.actual PUnit.unit.{1} d
    (@D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival d α inst Q n)

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"darkLayer_closure\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.darkLayer_closure, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"darkLayer_closure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.darkLayer_closure, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration).actual (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"GeneralInstrumentDarkClosure\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure, declaration := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
