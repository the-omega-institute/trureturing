import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.FixedSupportFisherGap
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

namespace Reg.D5.S3.Quantum.Information.FixedSupportFisherGap
open _root_.D5.S3.Quantum.Information.FixedSupportFisherGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Finset
open scoped BigOperators
noncomputable section
universe u

abbrev signature : Signature where
  Params := (ι : Type u) × (ι → ℝ → ℝ)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law O := ∀ {ι : Type u} [Fintype ι] (a R : ℝ) (x : ι → ℝ) (p : ι → ℝ → ℝ),
    0 < a → a < 1 →
    (∀ j, x j ∈ Icc (-1 : ℝ) 1) →
    (∀ u ∈ Ioo (2*a-1) 1, ∀ j, 0 ≤ p j u) →
    (∀ j, DifferentiableOn ℝ (p j) (Ioo (2*a-1) 1)) →
    (∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u = 1) →
    (∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u * x j = a) →
    (∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u * x j^2 = (1+u)/2) →
    (∀ u ∈ Ioo (2*a-1) 1,
      (∑ j ∈ univ.filter (fun j => 0 < p j u), (O.readout () ⟨ι,p⟩ j u)^2 / p j u) ≤
        R*(1-a^2)/((1-u)*(1+u-2*a^2))) →
    1 + a^2 / (1+4*a+2*(1+a)*Real.log 2)^2 ≤ R

def actual : Realization signature.{u} :=
  realize signature (fun _ p j => deriv (p.2 j)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

-- A single affine probability curve with all three moments, on the full open interval.
def support (j : ULift.{u} (Fin 3)) : ℝ := ![-1,0,1] j.down
def curve (j : ULift.{u} (Fin 3)) (t : ℝ) : ℝ := ![t/4,(1-t)/2,(2+t)/4] j.down

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hx : ∀ j, support.{u} j ∈ Icc (-1 : ℝ) 1 := by
    intro ⟨j⟩; fin_cases j <;> norm_num [support]
  have hp : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∀ j, 0 ≤ curve.{u} j t := by
    intro t ht ⟨j⟩
    have ht0 : 0 < t := by linarith [ht.1]
    fin_cases j <;> simp [curve] <;> linarith [ht.2]
  have hd : ∀ j, DifferentiableOn ℝ (curve.{u} j) (Ioo (2*(1/2 : ℝ)-1) 1) := by
    intro ⟨j⟩; fin_cases j <;> change DifferentiableOn ℝ (fun t => _) _ <;>
      dsimp [curve] <;> fun_prop
  have h0 : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∑ j, curve.{u} j t = 1 := by
    intro t _
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))]
    simp [curve, Fin.sum_univ_three]; ring
  have h1 : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∑ j, curve.{u} j t * support j = (1/2 : ℝ) := by
    intro t _
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))]
    simp [curve, support, Fin.sum_univ_three]; ring
  have h2 : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∑ j, curve.{u} j t * support j^2 = (1+t)/2 := by
    intro t _
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))]
    simp [curve, support, Fin.sum_univ_three]; ring
  have hh := h (1/2) 0 support curve (by norm_num) (by norm_num) hx hp hd h0 h1 h2
    (by intro t ht; simp [rejected, realize])
  have hn : 0 ≤ (1/2 : ℝ)^2 / (1+4*(1/2)+2*(1+1/2)*Real.log 2)^2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, (fun j t => if j.down then (0 : ℝ) else t)⟩,
      ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have he := congrFun h 0
    norm_num [actual, realize] at he

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Information.FixedSupportFisherGap.result.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1} (fun _ p j => deriv.{0, 0} (p.2 j)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "FixedSupportFisherGap") "result") "Reg.D5.S3.Quantum.Information.FixedSupportFisherGap/Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1} (fun _ p j => deriv.{0, 0} (p.2 j)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.FixedSupportFisherGap, definition := none, coordinates := #[0, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn", "arg", "fn"], stateBinder := 16, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `D5.S3.Quantum.Information.FixedSupportFisherGap.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.observationFact0, `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Quantum.Information.FixedSupportFisherGap


noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
      Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
      Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.actual.{u_1})
    Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `D5.S3.Quantum.Information.FixedSupportFisherGap.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.arena.{u_1}
    Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.actual.{u_1})
  Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.observation0.{u_1} : {ι : Type u_1} →
  [inst : Fintype.{u_1} ι] →
    (a R : Real) →
      (x : ι → Real) →
        (p : ι → Real → Real) →
          (ha :
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                a) →
            (ha1 :
                @LT.lt.{0} Real Real.instLT a
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              (hx :
                  ∀ (j : ι),
                    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                      (@Set.Icc.{0} Real Real.instPreorder
                        (@Neg.neg.{0} Real Real.instNeg
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (x j)) →
                (hp :
                    ∀ (u : Real),
                      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                          (@Set.Ioo.{0} Real Real.instPreorder
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                a)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          u →
                        ∀ (j : ι),
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (p j u)) →
                  (hd :
                      ∀ (j : ι),
                        @DifferentiableOn.{0, 0, 0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
                          Real.instAddCommGroup
                          (@Semiring.toModule.{0} Real
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@NontriviallyNormedField.toNormedField.{0} Real
                                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                        Real.denselyNormedField)))))))
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          Real Real.instAddCommGroup
                          (@Semiring.toModule.{0} Real
                            (@DivisionSemiring.toSemiring.{0} Real
                              (@Semifield.toDivisionSemiring.{0} Real
                                (@Field.toSemifield.{0} Real
                                  (@NormedField.toField.{0} Real
                                    (@NontriviallyNormedField.toNormedField.{0} Real
                                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                        Real.denselyNormedField)))))))
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (p j)
                          (@Set.Ioo.{0} Real Real.instPreorder
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                a)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                    (h0 :
                        ∀ (u : Real),
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                              (@Set.Ioo.{0} Real Real.instPreorder
                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    a)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                              u →
                            @Eq.{1} Real
                              (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst)
                                fun (j : ι) => p j u)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                      (h1 :
                          ∀ (u : Real),
                            @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                                (@Set.Ioo.{0} Real Real.instPreorder
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                          (@Nat.instAtLeastTwoHAddOfNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                            (@Nat.instNeZeroSucc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                      a)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                u →
                              @Eq.{1} Real
                                (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst)
                                  fun (j : ι) =>
                                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (p j u) (x j))
                                a) →
                        (h2 :
                            ∀ (u : Real),
                              @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                                  (@Set.Ioo.{0} Real Real.instPreorder
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        a)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                  u →
                                @Eq.{1} Real
                                  (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst)
                                    fun (j : ι) =>
                                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (p j u)
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat
                                          (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                        (x j) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                          (u : Real) →
                            @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                                (@Set.Ioo.{0} Real Real.instPreorder
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                          (@Nat.instAtLeastTwoHAddOfNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                            (@Nat.instNeZeroSucc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                      a)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                u →
                              (j : ι) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1,
                                    0, 0, 0}
                                  Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.signature.{u_1} PUnit.unit.{1}
                                  (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (ι : Type u_1) => ι → Real → Real) ι p) :=
  fun {ι : Type u_1} [Fintype.{u_1} ι] (a R : Real) (x : ι → Real) (p : ι → Real → Real)
    (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hx :
      ∀ (j : ι),
        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (x j))
    (hp :
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
          ∀ (j : ι),
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (p j u))
    (hd :
      ∀ (j : ι),
        @DifferentiableOn.{0, 0, 0} Real
          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real Real.instAddCommGroup
          (@Semiring.toModule.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real Real.instAddCommGroup
          (@Semiring.toModule.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (p j)
          (@Set.Ioo.{0} Real Real.instPreorder
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                a)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (h0 :
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
          @Eq.{1} Real
            (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (j : ι) => p j u)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (h1 :
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
          @Eq.{1} Real
            (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (j : ι) =>
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (p j u) (x j))
            a)
    (h2 :
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
          @Eq.{1} Real
            (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (j : ι) =>
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (p j u)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (x j)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (u : Real)
    (a_1 :
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
        u)
    (j : ι) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.signature.{u_1}
    Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (ι : Type u_1) => ι → Real → Real) ι p) j

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `D5.S3.Quantum.Information.FixedSupportFisherGap.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .domain, .body, .body, .function, .argument, .argument, .body, .function, .argument, .function, .argument, .function], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `D5.S3.Quantum.Information.FixedSupportFisherGap.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration.{u_1}).actual (Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"FixedSupportFisherGap\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap, declaration := `Reg.D5.S3.Quantum.Information.FixedSupportFisherGap.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
