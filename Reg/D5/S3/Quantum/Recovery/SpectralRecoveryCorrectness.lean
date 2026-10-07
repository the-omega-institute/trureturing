import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
universe u v w z

abbrev signature : Signature where
  Params := Type z
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{z} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{z} :=
  realize signature (fun _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{z}
  Law r := ∀ {s : Type u} {t : Type v} {n : Type w} {d : Type z}
    [Fintype s] [DecidableEq s] [Fintype t]
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    (E : s → Matrix n d ℂ) (hTP : (∑ a, (E a)ᴴ * E a) = 1)
    (A : t → Matrix d n ℂ) (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (v : d) (X : Matrix d d ℂ),
    spectralRecoveryAction E v (∑ a, E a * X * (E a)ᴴ) = r.readout () d X

theorem actual_law : arena.{u,v,w,z}.Law actual := by
  intro s t n d _ _ _ _ _ _ _ E hTP A hA hleft v X
  exact computed_recovery_of_kraus_left_inverse E hTP A hA hleft v X

theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let E : ULift.{u} (Fin 1) → Matrix (ULift.{w} (Fin 1)) (ULift.{z} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  let A : ULift.{v} (Fin 1) → Matrix (ULift.{z} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hTP : (∑ a, (E a)ᴴ * E a) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [E, Matrix.one_apply, Subsingleton.elim i j]
  have hA : (∑ b, (A b)ᴴ * A b) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [A, Matrix.one_apply, Subsingleton.elim i j]
  have hleft : ∀ X : Matrix (ULift.{z} (Fin 1)) (ULift.{z} (Fin 1)) ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X := by
    intro X
    ext i j
    have hi : i = ULift.up 0 := Subsingleton.elim _ _
    have hj : j = ULift.up 0 := Subsingleton.elim _ _
    subst i; subst j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [A, E]
    congr 1
  have heq := h E hTP A hA hleft (ULift.up 0) 0
  have hz : (0 : Matrix (ULift.{z} (Fin 1)) (ULift.{z} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [spectralRecoveryAction, rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v,w,z} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{z} (Fin 1), (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

noncomputable def registration_1.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse.{u_1, u_2, u_3, u_4}) (type_of% (realize.{u_4 + 1, u_4, 0, u_4, 0} signature.{u_4} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "SpectralRecoveryCorrectness") "computed_recovery_of_kraus_left_inverse") "Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness/Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3, u_4})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3, u_4})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3, u_4}) ⟨(registration.{u_1, u_2, u_3, u_4})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_4 + 1, u_4, 0, u_4, 0} signature.{u_4} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, definition := none, coordinates := #[3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 17, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] }], facts := [`Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness


noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalArenaOperand.{u_1, u_2, u_3, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_4 + 1, u_4, 0, u_4, 0} :=
  Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.arena.{u_1, u_2, u_3, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalArenaFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_4 + 1, u_4, 0, u_4, 0} :=
  Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.arena.{u_1, u_2, u_3, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.sourceLaw.{u_1, u_2, u_3, u_4} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_4 + 1, u_4, 0, u_4, 0} (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.arena.) (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration.{u_1, u_2, u_3, u_4}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.sourceBridgeFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"computed_recovery_of_kraus_left_inverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration.{u_1, u_2, u_3, u_4}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.observation0.{u_1, u_2, u_3, u_4} : {s : Type u_1} →
  {t : Type u_2} →
    {n : Type u_3} →
      {d : Type u_4} →
        [inst : Fintype.{u_1} s] →
          [DecidableEq.{u_1 + 1} s] →
            [inst_2 : Fintype.{u_2} t] →
              [inst_3 : Fintype.{u_3} n] →
                [inst_4 : DecidableEq.{u_3 + 1} n] →
                  [inst_5 : Fintype.{u_4} d] →
                    [inst_6 : DecidableEq.{u_4 + 1} d] →
                      (E : s → Matrix.{u_3, u_4, 0} n d Complex) →
                        (hTP :
                            @Eq.{u_4 + 1} (Matrix.{u_4, u_4, 0} d d Complex)
                              (@Finset.sum.{u_1, u_4} s (Matrix.{u_4, u_4, 0} d d Complex)
                                (@Matrix.addCommMonoid.{0, u_4, u_4} d d Complex Complex.instAddCommMonoid)
                                (@Finset.univ.{u_1} s inst) fun (a : s) =>
                                @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_4} (Matrix.{u_4, u_3, 0} d n Complex)
                                  (Matrix.{u_3, u_4, 0} n d Complex) (Matrix.{u_4, u_4, 0} d d Complex)
                                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_4, u_3, u_4} d n d Complex inst_3
                                    Complex.instMul Complex.instAddCommMonoid)
                                  (@Matrix.conjTranspose.{0, u_3, u_4} n d Complex
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
                                    (E a))
                                  (E a))
                              (@OfNat.ofNat.{u_4} (Matrix.{u_4, u_4, 0} d d Complex) (nat_lit 1)
                                (@One.toOfNat1.{u_4} (Matrix.{u_4, u_4, 0} d d Complex)
                                  (@Matrix.one.{0, u_4} d Complex inst_6 Complex.instZero Complex.instOne)))) →
                          (A : t → Matrix.{u_4, u_3, 0} d n Complex) →
                            (hA :
                                @Eq.{u_3 + 1} (Matrix.{u_3, u_3, 0} n n Complex)
                                  (@Finset.sum.{u_2, u_3} t (Matrix.{u_3, u_3, 0} n n Complex)
                                    (@Matrix.addCommMonoid.{0, u_3, u_3} n n Complex Complex.instAddCommMonoid)
                                    (@Finset.univ.{u_2} t inst_2) fun (b : t) =>
                                    @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_3} (Matrix.{u_3, u_4, 0} n d Complex)
                                      (Matrix.{u_4, u_3, 0} d n Complex) (Matrix.{u_3, u_3, 0} n n Complex)
                                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_4, u_3} n d n Complex
                                        inst_5 Complex.instMul Complex.instAddCommMonoid)
                                      (@Matrix.conjTranspose.{0, u_4, u_3} d n Complex
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
                                        (A b))
                                      (A b))
                                  (@OfNat.ofNat.{u_3} (Matrix.{u_3, u_3, 0} n n Complex) (nat_lit 1)
                                    (@One.toOfNat1.{u_3} (Matrix.{u_3, u_3, 0} n n Complex)
                                      (@Matrix.one.{0, u_3} n Complex inst_4 Complex.instZero Complex.instOne)))) →
                              (hleft :
                                  ∀ (X : Matrix.{u_4, u_4, 0} d d Complex),
                                    @Eq.{u_4 + 1} (Matrix.{u_4, u_4, 0} d d Complex)
                                      (@Finset.sum.{u_2, u_4} t (Matrix.{u_4, u_4, 0} d d Complex)
                                        (@Matrix.addCommMonoid.{0, u_4, u_4} d d Complex Complex.instAddCommMonoid)
                                        (@Finset.univ.{u_2} t inst_2) fun (b : t) =>
                                        @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_4} (Matrix.{u_4, u_3, 0} d n Complex)
                                          (Matrix.{u_3, u_4, 0} n d Complex) (Matrix.{u_4, u_4, 0} d d Complex)
                                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_4, u_3, u_4} d n d
                                            Complex inst_3 Complex.instMul Complex.instAddCommMonoid)
                                          (@HMul.hMul.{max u_3 u_4, u_3, max u_3 u_4} (Matrix.{u_4, u_3, 0} d n Complex)
                                            (Matrix.{u_3, u_3, 0} n n Complex) (Matrix.{u_4, u_3, 0} d n Complex)
                                            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_4, u_3, u_3} d n n
                                              Complex inst_3 Complex.instMul Complex.instAddCommMonoid)
                                            (A b)
                                            (@Finset.sum.{u_1, u_3} s (Matrix.{u_3, u_3, 0} n n Complex)
                                              (@Matrix.addCommMonoid.{0, u_3, u_3} n n Complex
                                                Complex.instAddCommMonoid)
                                              (@Finset.univ.{u_1} s inst) fun (a : s) =>
                                              @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_3}
                                                (Matrix.{u_3, u_4, 0} n d Complex) (Matrix.{u_4, u_3, 0} d n Complex)
                                                (Matrix.{u_3, u_3, 0} n n Complex)
                                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_4, u_3} n d n
                                                  Complex inst_5 Complex.instMul Complex.instAddCommMonoid)
                                                (@HMul.hMul.{max u_3 u_4, u_4, max u_3 u_4}
                                                  (Matrix.{u_3, u_4, 0} n d Complex) (Matrix.{u_4, u_4, 0} d d Complex)
                                                  (Matrix.{u_3, u_4, 0} n d Complex)
                                                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_4, u_4} n d
                                                    d Complex inst_5 Complex.instMul Complex.instAddCommMonoid)
                                                  (E a) X)
                                                (@Matrix.conjTranspose.{0, u_3, u_4} n d Complex
                                                  (@InvolutiveStar.toStar.{0} Complex
                                                    (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                                      (@AddCommMonoid.toAddMonoid.{0} Complex
                                                        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0}
                                                            Complex
                                                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0}
                                                              Complex
                                                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0}
                                                                Complex Complex.instNonUnitalCommRing)))))
                                                      (@StarRing.toStarAddMonoid.{0} Complex
                                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0}
                                                            Complex
                                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                              Complex.instNonUnitalCommRing)))
                                                        Complex.instStarRing)))
                                                  (E a))))
                                          (@Matrix.conjTranspose.{0, u_4, u_3} d n Complex
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
                                            (A b)))
                                      X) →
                                (v : d) →
                                  (X : Matrix.{u_4, u_4, 0} d d Complex) →
                                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_4 + 1,
                                        u_4, 0, u_4, 0}
                                      Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.signature.{u_4} Unit.unit d :=
  fun {s : Type u_1} {t : Type u_2} {n : Type u_3} {d : Type u_4} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s]
    [Fintype.{u_2} t] [Fintype.{u_3} n] [DecidableEq.{u_3 + 1} n] [Fintype.{u_4} d] [DecidableEq.{u_4 + 1} d]
    (E : s → Matrix.{u_3, u_4, 0} n d Complex)
    (hTP :
      @Eq.{u_4 + 1} (Matrix.{u_4, u_4, 0} d d Complex)
        (@Finset.sum.{u_1, u_4} s (Matrix.{u_4, u_4, 0} d d Complex)
          (@Matrix.addCommMonoid.{0, u_4, u_4} d d Complex Complex.instAddCommMonoid) (@Finset.univ.{u_1} s inst)
          fun (a : s) =>
          @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_4} (Matrix.{u_4, u_3, 0} d n Complex)
            (Matrix.{u_3, u_4, 0} n d Complex) (Matrix.{u_4, u_4, 0} d d Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_4, u_3, u_4} d n d Complex inst_3 Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, u_3, u_4} n d Complex
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
              (E a))
            (E a))
        (@OfNat.ofNat.{u_4} (Matrix.{u_4, u_4, 0} d d Complex) (nat_lit 1)
          (@One.toOfNat1.{u_4} (Matrix.{u_4, u_4, 0} d d Complex)
            (@Matrix.one.{0, u_4} d Complex inst_6 Complex.instZero Complex.instOne))))
    (A : t → Matrix.{u_4, u_3, 0} d n Complex)
    (hA :
      @Eq.{u_3 + 1} (Matrix.{u_3, u_3, 0} n n Complex)
        (@Finset.sum.{u_2, u_3} t (Matrix.{u_3, u_3, 0} n n Complex)
          (@Matrix.addCommMonoid.{0, u_3, u_3} n n Complex Complex.instAddCommMonoid) (@Finset.univ.{u_2} t inst_2)
          fun (b : t) =>
          @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_3} (Matrix.{u_3, u_4, 0} n d Complex)
            (Matrix.{u_4, u_3, 0} d n Complex) (Matrix.{u_3, u_3, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_4, u_3} n d n Complex inst_5 Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, u_4, u_3} d n Complex
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
              (A b))
            (A b))
        (@OfNat.ofNat.{u_3} (Matrix.{u_3, u_3, 0} n n Complex) (nat_lit 1)
          (@One.toOfNat1.{u_3} (Matrix.{u_3, u_3, 0} n n Complex)
            (@Matrix.one.{0, u_3} n Complex inst_4 Complex.instZero Complex.instOne))))
    (hleft :
      ∀ (X : Matrix.{u_4, u_4, 0} d d Complex),
        @Eq.{u_4 + 1} (Matrix.{u_4, u_4, 0} d d Complex)
          (@Finset.sum.{u_2, u_4} t (Matrix.{u_4, u_4, 0} d d Complex)
            (@Matrix.addCommMonoid.{0, u_4, u_4} d d Complex Complex.instAddCommMonoid) (@Finset.univ.{u_2} t inst_2)
            fun (b : t) =>
            @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_4} (Matrix.{u_4, u_3, 0} d n Complex)
              (Matrix.{u_3, u_4, 0} n d Complex) (Matrix.{u_4, u_4, 0} d d Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_4, u_3, u_4} d n d Complex inst_3 Complex.instMul
                Complex.instAddCommMonoid)
              (@HMul.hMul.{max u_3 u_4, u_3, max u_3 u_4} (Matrix.{u_4, u_3, 0} d n Complex)
                (Matrix.{u_3, u_3, 0} n n Complex) (Matrix.{u_4, u_3, 0} d n Complex)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_4, u_3, u_3} d n n Complex inst_3 Complex.instMul
                  Complex.instAddCommMonoid)
                (A b)
                (@Finset.sum.{u_1, u_3} s (Matrix.{u_3, u_3, 0} n n Complex)
                  (@Matrix.addCommMonoid.{0, u_3, u_3} n n Complex Complex.instAddCommMonoid)
                  (@Finset.univ.{u_1} s inst) fun (a : s) =>
                  @HMul.hMul.{max u_3 u_4, max u_3 u_4, u_3} (Matrix.{u_3, u_4, 0} n d Complex)
                    (Matrix.{u_4, u_3, 0} d n Complex) (Matrix.{u_3, u_3, 0} n n Complex)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_4, u_3} n d n Complex inst_5
                      Complex.instMul Complex.instAddCommMonoid)
                    (@HMul.hMul.{max u_3 u_4, u_4, max u_3 u_4} (Matrix.{u_3, u_4, 0} n d Complex)
                      (Matrix.{u_4, u_4, 0} d d Complex) (Matrix.{u_3, u_4, 0} n d Complex)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_4, u_4} n d d Complex inst_5
                        Complex.instMul Complex.instAddCommMonoid)
                      (E a) X)
                    (@Matrix.conjTranspose.{0, u_3, u_4} n d Complex
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
                      (E a))))
              (@Matrix.conjTranspose.{0, u_4, u_3} d n Complex
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
                (A b)))
          X)
    (v : d) (X : Matrix.{u_4, u_4, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_4 + 1, u_4, 0, u_4, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.signature.{u_4}
    Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.actual.{u_4} Unit.unit d X

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.observationFact0.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"computed_recovery_of_kraus_left_inverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.varyingLawInput.{u_1, u_2, u_3, u_4} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.canonicalArenaOperand.{u_1, u_2, u_3, u_4})
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.varyingLaw.{u_1, u_2, u_3, u_4}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.statementExclusion.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"computed_recovery_of_kraus_left_inverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration.{u_1, u_2, u_3, u_4}).actual (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration.{u_1, u_2, u_3, u_4}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration.{u_1, u_2, u_3, u_4}).variation.1 (Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration.{u_1, u_2, u_3, u_4}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1.descriptorFact.{u_4} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralRecoveryCorrectness\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))
