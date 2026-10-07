import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FiniteKrausReversibility
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FiniteKrausReversibility
open LeanInformationAudit Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility
universe v w u

abbrev signature : Signature where
  Params := Type u
  State d := Matrix d d ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ d := Matrix d d ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {s : Type v} {n : Type w} {d : Type u}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]
    [Fintype d] [DecidableEq d]
    (E : s → Matrix n d ℂ) (hTP : (∑ a, (E a)ᴴ * E a) = 1)
    (v : d) (c : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)),
    ∃ r : ℕ, ∃ A : Fin r → Matrix d n ℂ,
      (∑ b, (A b)ᴴ * A b) = 1 ∧
      ∀ X : Matrix d d ℂ,
        (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = R.readout () d X

theorem actual_law : arena.{v,w,u}.Law actual := by
  intro s n d _ _ _ _ _ _ E hTP v c hE
  exact scalar_products_construct_left_inverse E hTP v c hE

theorem rejected_law : ¬ arena.{v,w,u}.Law rejected := by
  intro h
  let s := ULift.{v} (Fin 1)
  let n := ULift.{w} (Fin 1)
  let d := ULift.{u} (Fin 1)
  let i : d := ⟨0⟩
  let E : s → Matrix n d ℂ := fun _ _ _ => 1
  have hTP : (∑ a, (E a)ᴴ * E a) = 1 := by
    ext j k
    change (∑ _a : s, ∑ _b : n, star (1 : ℂ) * 1) = (1 : Matrix d d ℂ) j k
    simp [Matrix.one_apply, Subsingleton.elim j k]
  have hE : ∀ a b, (E a)ᴴ * E b = (1 : ℂ) • (1 : Matrix d d ℂ) := by
    intro a b
    ext j k
    change (∑ _b : n, star (1 : ℂ) * 1) = (1 : ℂ) * (1 : Matrix d d ℂ) j k
    simp [Matrix.one_apply, Subsingleton.elim j k]
  obtain ⟨r, A, _, hrec⟩ := h E hTP i (fun _ _ => 1) hE
  have hzero := hrec (0 : Matrix d d ℂ)
  have hentry := congrArg (fun M : Matrix d d ℂ => M i i) hzero
  norm_num [rejected, realize, signature] at hentry

def registration : Registration arena.{v,w,u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let d := ULift.{u} (Fin 1)
    let i : d := ⟨0⟩
    refine ⟨d, (0 : Matrix d d ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix d d ℂ => M i i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.FiniteKrausReversibility.scalar_products_construct_left_inverse.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} signature.{u_3} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "FiniteKrausReversibility") "scalar_products_construct_left_inverse") "Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility/Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} signature.{u_3} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.FiniteKrausReversibility, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg"], stateBinder := 16, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `D5.S3.Quantum.Recovery.FiniteKrausReversibility.scalar_products_construct_left_inverse, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.arena.) (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"scalar_products_construct_left_inverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `D5.S3.Quantum.Recovery.FiniteKrausReversibility.scalar_products_construct_left_inverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [inst : Fintype.{u_1} s] →
        [DecidableEq.{u_1 + 1} s] →
          [inst_2 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              [Fintype.{u_3} d] →
                [inst_5 : DecidableEq.{u_3 + 1} d] →
                  (E : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hTP :
                        @Eq.{u_3 + 1} (Matrix.{u_3, u_3, 0} d d Complex)
                          (@Finset.sum.{u_1, u_3} s (Matrix.{u_3, u_3, 0} d d Complex)
                            (@Matrix.addCommMonoid.{0, u_3, u_3} d d Complex Complex.instAddCommMonoid)
                            (@Finset.univ.{u_1} s inst) fun (a : s) =>
                            @HMul.hMul.{max u_2 u_3, max u_2 u_3, u_3} (Matrix.{u_3, u_2, 0} d n Complex)
                              (Matrix.{u_2, u_3, 0} n d Complex) (Matrix.{u_3, u_3, 0} d d Complex)
                              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_2, u_3} d n d Complex inst_2
                                Complex.instMul Complex.instAddCommMonoid)
                              (@Matrix.conjTranspose.{0, u_2, u_3} n d Complex
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
                          (@OfNat.ofNat.{u_3} (Matrix.{u_3, u_3, 0} d d Complex) (nat_lit 1)
                            (@One.toOfNat1.{u_3} (Matrix.{u_3, u_3, 0} d d Complex)
                              (@Matrix.one.{0, u_3} d Complex inst_5 Complex.instZero Complex.instOne)))) →
                      (v : d) →
                        (c : Matrix.{u_1, u_1, 0} s s Complex) →
                          (hE :
                              ∀ (a b : s),
                                @Eq.{u_3 + 1} (Matrix.{u_3, u_3, 0} d d Complex)
                                  (@HMul.hMul.{max u_2 u_3, max u_2 u_3, u_3} (Matrix.{u_3, u_2, 0} d n Complex)
                                    (Matrix.{u_2, u_3, 0} n d Complex) (Matrix.{u_3, u_3, 0} d d Complex)
                                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_2, u_3} d n d Complex
                                      inst_2 Complex.instMul Complex.instAddCommMonoid)
                                    (@Matrix.conjTranspose.{0, u_2, u_3} n d Complex
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
                                    (E b))
                                  (@HSMul.hSMul.{0, u_3, u_3} Complex (Matrix.{u_3, u_3, 0} d d Complex)
                                    (Matrix.{u_3, u_3, 0} d d Complex)
                                    (@instHSMul.{0, u_3} Complex (Matrix.{u_3, u_3, 0} d d Complex)
                                      (@Matrix.smul.{0, u_3, u_3, 0} d d Complex Complex
                                        (@instSMulOfMul.{0} Complex Complex.instMul)))
                                    (c a b)
                                    (@OfNat.ofNat.{u_3} (Matrix.{u_3, u_3, 0} d d Complex) (nat_lit 1)
                                      (@One.toOfNat1.{u_3} (Matrix.{u_3, u_3, 0} d d Complex)
                                        (@Matrix.one.{0, u_3} d Complex inst_5 Complex.instZero Complex.instOne))))) →
                            (r : Nat) →
                              (A : Fin r → Matrix.{u_3, u_2, 0} d n Complex) →
                                (X : Matrix.{u_3, u_3, 0} d d Complex) →
                                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1,
                                      u_3, 0, u_3, 0}
                                    Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.signature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (E : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hTP :
      @Eq.{u_3 + 1} (Matrix.{u_3, u_3, 0} d d Complex)
        (@Finset.sum.{u_1, u_3} s (Matrix.{u_3, u_3, 0} d d Complex)
          (@Matrix.addCommMonoid.{0, u_3, u_3} d d Complex Complex.instAddCommMonoid) (@Finset.univ.{u_1} s inst)
          fun (a : s) =>
          @HMul.hMul.{max u_2 u_3, max u_2 u_3, u_3} (Matrix.{u_3, u_2, 0} d n Complex)
            (Matrix.{u_2, u_3, 0} n d Complex) (Matrix.{u_3, u_3, 0} d d Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_2, u_3} d n d Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, u_2, u_3} n d Complex
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
        (@OfNat.ofNat.{u_3} (Matrix.{u_3, u_3, 0} d d Complex) (nat_lit 1)
          (@One.toOfNat1.{u_3} (Matrix.{u_3, u_3, 0} d d Complex)
            (@Matrix.one.{0, u_3} d Complex inst_5 Complex.instZero Complex.instOne))))
    (v : d) (c : Matrix.{u_1, u_1, 0} s s Complex)
    (hE :
      ∀ (a b : s),
        @Eq.{u_3 + 1} (Matrix.{u_3, u_3, 0} d d Complex)
          (@HMul.hMul.{max u_2 u_3, max u_2 u_3, u_3} (Matrix.{u_3, u_2, 0} d n Complex)
            (Matrix.{u_2, u_3, 0} n d Complex) (Matrix.{u_3, u_3, 0} d d Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_3, u_2, u_3} d n d Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, u_2, u_3} n d Complex
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
            (E b))
          (@HSMul.hSMul.{0, u_3, u_3} Complex (Matrix.{u_3, u_3, 0} d d Complex) (Matrix.{u_3, u_3, 0} d d Complex)
            (@instHSMul.{0, u_3} Complex (Matrix.{u_3, u_3, 0} d d Complex)
              (@Matrix.smul.{0, u_3, u_3, 0} d d Complex Complex (@instSMulOfMul.{0} Complex Complex.instMul)))
            (c a b)
            (@OfNat.ofNat.{u_3} (Matrix.{u_3, u_3, 0} d d Complex) (nat_lit 1)
              (@One.toOfNat1.{u_3} (Matrix.{u_3, u_3, 0} d d Complex)
                (@Matrix.one.{0, u_3} d Complex inst_5 Complex.instZero Complex.instOne)))))
    (r : Nat) (A : Fin r → Matrix.{u_3, u_2, 0} d n Complex) (X : Matrix.{u_3, u_3, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.signature.{u_3}
    Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.actual.{u_3} Unit.unit d X

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"scalar_products_construct_left_inverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `D5.S3.Quantum.Recovery.FiniteKrausReversibility.scalar_products_construct_left_inverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"scalar_products_construct_left_inverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `D5.S3.Quantum.Recovery.FiniteKrausReversibility.scalar_products_construct_left_inverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteKrausReversibility\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
