import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ContinuationEffectClosure
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.ContinuationEffectClosure
open LeanInformationAudit Matrix Filter Topology

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ W => W) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {J : Type} {κ : J → Type} [∀ j, Fintype (κ j)]
    (K : (j : J) → κ j → Matrix (Fin d) (Fin d) ℂ)
    (Z₀ : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) (hZ₀ : ∀ H ∈ Z₀, Hᴴ = H),
    (∀ n, d ^ 2 - Module.finrank ℝ Z₀ ≤ n →
        continuationSpace K Z₀ n = continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀)) ∧
      Z₀ ≤ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀) ∧
      (∀ j, ∀ H ∈ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀),
        branchDual K j H ∈ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀)) ∧
      ∀ W : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ), Z₀ ≤ W →
        (∀ j, ∀ H ∈ W, branchDual K j H ∈ W) →
          continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀) ≤ R.readout () d W

theorem actual_law : arena.Law actual := by
  intro d J κ _ K Z₀ hZ₀
  exact continuationSpace_closure K Z₀ hZ₀

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K : (j : Unit) → Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 0
  let Z₀ : Submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) := Submodule.span ℝ {1}
  have hZ₀ : ∀ H ∈ Z₀, Hᴴ = H := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem X hX =>
        have : X = 1 := Set.mem_singleton_iff.mp hX
        subst X
        exact Matrix.conjTranspose_one
    | zero => exact Matrix.conjTranspose_zero
    | add X Y _ _ hX hY => rw [Matrix.conjTranspose_add, hX, hY]
    | smul r X _ hX =>
        rw [Matrix.conjTranspose_smul, hX]
        congr 1
  have hgood : ∀ n, Z₀ ≤ continuationSpace K Z₀ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact le_trans ih le_sup_left
  have hbad := (h K Z₀ hZ₀).2.2.2 ⊤ le_top (fun _ _ _ => Submodule.mem_top)
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Z₀ := Submodule.subset_span rfl
  have hz : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := hbad (hgood _ h1)
  have he := congrFun (congrFun hz 0) 0
  norm_num at he

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
  exact ⟨1, ⊥, ⊤, bot_ne_top⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.ContinuationEffectClosure.continuationSpace_closure) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ W => W) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "ContinuationEffectClosure") "continuationSpace_closure") "Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure/Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ W => W) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.ContinuationEffectClosure, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `D5.S3.Quantum.Measurement.ContinuationEffectClosure.continuationSpace_closure, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure


noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.arena) (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration).actual

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"continuationSpace_closure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `D5.S3.Quantum.Measurement.ContinuationEffectClosure.continuationSpace_closure, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.observation0 : {d : Nat} →
  {J : Type} →
    {κ : J → Type} →
      [inst : (j : J) → Fintype.{0} (κ j)] →
        (K : (j : J) → κ j → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (Z₀ :
              @Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                      instInnerProductSpaceRealComplex)))) →
            (hZ₀ :
                ∀ (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex),
                  @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                        (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                        (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                      (@SetLike.instMembership.{0, 0}
                        (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                          (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                        (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                        (@Submodule.setLike.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                          (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                                instInnerProductSpaceRealComplex)))))
                      Z₀ H →
                    @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
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
                        H)
                      H) →
              (W :
                  @Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                    (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                    (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                          instInnerProductSpaceRealComplex)))) →
                @LE.le.{0}
                    (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                      (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                      (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                    (@Preorder.toLE.{0}
                      (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                        (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                        (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                      (@PartialOrder.toPreorder.{0}
                        (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                          (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                        (@Submodule.instPartialOrder.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          Real.semiring
                          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                          (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                                instInnerProductSpaceRealComplex))))))
                    Z₀ W →
                  (∀ (j : J) (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex),
                      @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                            (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))))
                            (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                            (@Submodule.setLike.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex)))))
                          W H →
                        @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                          (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                            (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
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
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  instInnerProductSpaceRealComplex))))
                          (@SetLike.instMembership.{0, 0}
                            (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))))
                            (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                            (@Submodule.setLike.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex)))))
                          W
                          (@DFunLike.coe.{1, 1, 1}
                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex)))
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))))
                            (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                            (fun (x : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) =>
                              Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring Real.semiring
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex)))
                              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring
                                Complex.instAddCommMonoid
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex)))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            (@D5.S3.Quantum.Measurement.ContinuationEffectClosure.branchDual d J κ inst K j) H)) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.signature PUnit.unit.{1} d :=
  fun {d : Nat} {J : Type} {κ : J → Type} [(j : J) → Fintype.{0} (κ j)]
    (K : (j : J) → κ j → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (Z₀ :
      @Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
        (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
        (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
    (hZ₀ :
      ∀ (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex),
        @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Submodule.setLike.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                      instInnerProductSpaceRealComplex)))))
            Z₀ H →
          @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
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
              H)
            H)
    (W :
      @Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
        (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
        (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
    (a :
      @LE.le.{0}
        (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
          (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
          (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
        (@Preorder.toLE.{0}
          (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
          (@PartialOrder.toPreorder.{0}
            (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
            (@Submodule.instPartialOrder.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                    instInnerProductSpaceRealComplex))))))
        Z₀ W)
    (a_1 :
      ∀ (j : J) (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex),
        @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Submodule.setLike.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                      instInnerProductSpaceRealComplex)))))
            W H →
          @Membership.mem.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
              (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
              (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Submodule.setLike.{0, 0} Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                      instInnerProductSpaceRealComplex)))))
            W
            (@DFunLike.coe.{1, 1, 1}
              (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (fun (x : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) Real.semiring Real.semiring
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
                (@Matrix.module.{0, 0, 0, 0} (Fin d) (Fin d) Real Complex Real.semiring Complex.instAddCommMonoid
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
              (@D5.S3.Quantum.Measurement.ContinuationEffectClosure.branchDual d J κ inst K j) H)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.signature
    Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.actual PUnit.unit.{1} d W

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"continuationSpace_closure\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `D5.S3.Quantum.Measurement.ContinuationEffectClosure.continuationSpace_closure, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"continuationSpace_closure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `D5.S3.Quantum.Measurement.ContinuationEffectClosure.continuationSpace_closure, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration).actual (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ContinuationEffectClosure\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure, declaration := `Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
