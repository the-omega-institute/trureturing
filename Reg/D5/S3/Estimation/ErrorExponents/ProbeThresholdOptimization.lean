import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization

universe u

def signature : Signature where
  Params := Σ ι : Type u, Σ _ : ι → ℝ, ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p l => Real.sqrt (p.2.1 l)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

open scoped Classical in
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (_ha : ∀ l, 0 < a l) (_hsum : ∑ l, a l = 1)
    (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1),
    let v : ι → ℝ := fun l => R.readout () ⟨ι, a, ε⟩ l
    let F : (ι → ℝ) → ℝ := fun x => (∑ l, v l * x l) ^ 2 - ε * ∑ l, (x l) ^ 2
    let X : ℝ → ι → ℝ := fun c l => min 1 (c * v l)
    let H : ℝ → Finset ι := fun c => Finset.univ.filter fun l => 1 ≤ c * v l
    let d : ℝ → ℝ := fun c =>
      ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), a l
    let S : ℝ → ℝ := fun c => ∑ l ∈ H c, v l
    ∃ c : ℝ,
      (0 < c ∧
        (∑ l, min (a l) (v l / c)) = ε ∧
        (∀ l, 0 ≤ X c l ∧ X c l ≤ 1) ∧
        (∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c)) ∧
        d c < ε ∧
        c = S c / (ε - d c) ∧
        F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card) ∧
      (∀ c', 0 < c' → (∑ l, min (a l) (v l / c')) = ε → c' = c)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have ht := h (ι := ULift.{u} Unit)
    (a := fun _ : ULift.{u} Unit => (1 : ℝ))
    (by intro; norm_num) (by simp) (1 / 2) (by norm_num) (by norm_num)
  dsimp [rejected, realize, signature] at ht
  obtain ⟨c, hc, _⟩ := ht
  have hroot := hc.2.1
  norm_num at hroot

open scoped Classical in
def registration : Registration arena.{u} (∀ {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (_ha : ∀ l, 0 < a l) (_hsum : ∑ l, a l = 1)
    (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1),
    let v : ι → ℝ := fun l => Real.sqrt (a l)
    let F : (ι → ℝ) → ℝ := fun x => (∑ l, v l * x l) ^ 2 - ε * ∑ l, (x l) ^ 2
    let X : ℝ → ι → ℝ := fun c l => min 1 (c * v l)
    let H : ℝ → Finset ι := fun c => Finset.univ.filter fun l => 1 ≤ c * v l
    let d : ℝ → ℝ := fun c =>
      ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), a l
    let S : ℝ → ℝ := fun c => ∑ l ∈ H c, v l
    ∃ c : ℝ,
      (0 < c ∧
        (∑ l, min (a l) (v l / c)) = ε ∧
        (∀ l, 0 ≤ X c l ∧ X c l ≤ 1) ∧
        (∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c)) ∧
        d c < ε ∧
        c = S c / (ε - d c) ∧
        F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card) ∧
      (∀ c', 0 < c' → (∑ l, min (a l) (v l / c')) = ε → c' = c)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨probe_threshold_optimization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 2),
        (fun l => if l.down = 0 then (0 : ℝ) else 1), (1 / 2 : ℝ)⟩,
      ULift.up (0 : Fin 2), ULift.up (1 : Fin 2), ?_⟩
    dsimp [arena, actual, realize, signature]
    norm_num

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.probe_threshold_optimization.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1}
    (fun _ p l => Real.sqrt (p.2.1 l)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "ErrorExponents") "ProbeThresholdOptimization") "probe_threshold_optimization") "Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization/Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1}
    (fun _ p l => Real.sqrt (p.2.1 l)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, definition := none, coordinates := #[0, 2, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "value", "body"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.probe_threshold_optimization, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.observationFact0, `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.anchorEnumeration }


#print axioms rejected_law

end Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization


noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.arena.{u_1}
    (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] (a : ι → Real)
      (_ha :
        ∀ (l : ι),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (a l))
      (_hsum :
        @Eq.{1} Real (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) => a l)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (ε : Real)
      (_hε0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
      (_hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
      have v : ι → Real := fun (l : ι) => Real.sqrt (a l);
      have F : (ι → Real) → Real := fun (x : ι → Real) =>
        @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (v l) (x l))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
            (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
              @HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (x l)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))));
      have X : Real → ι → Real := fun (c : Real) (l : ι) =>
        @Min.min.{0} Real Real.instMin (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c (v l));
      have H : Real → Finset.{u_1} ι := fun (c : Real) =>
        @Finset.filter.{u_1} ι
          (fun (l : ι) =>
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c (v l)))
          (fun (a : ι) =>
            Real.decidableLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c (v a)))
          (@Finset.univ.{u_1} ι inst);
      have d : Real → Real := fun (c : Real) =>
        @Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid
          (@Finset.filter.{u_1} ι
            (fun (l : ι) =>
              Not
                (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
                  (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) (H c) l))
            (fun (a : ι) =>
              @instDecidableNot
                (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
                  (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) (H c) a)
                (@Finset.decidableMem.{u_1} ι (fun (a b : ι) => Classical.propDecidable (@Eq.{u_1 + 1} ι a b)) a (H c)))
            (@Finset.univ.{u_1} ι inst))
          fun (l : ι) => a l;
      have S : Real → Real := fun (c : Real) =>
        @Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (H c) fun (l : ι) => v l;
      @Exists.{1} Real fun (c : Real) =>
        And
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
            (And
              (@Eq.{1} Real
                (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
                  @Min.min.{0} Real Real.instMin (a l)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (v l) c))
                ε)
              (And
                (∀ (l : ι),
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (X c l))
                    (@LE.le.{0} Real Real.instLE (X c l)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                (And
                  (∀ (x : ι → Real),
                    (∀ (l : ι),
                        And
                          (@LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (x l))
                          (@LE.le.{0} Real Real.instLE (x l)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                      @LE.le.{0} Real Real.instLE (F x) (F (X c)))
                  (And (@LT.lt.{0} Real Real.instLT (d c) ε)
                    (And
                      (@Eq.{1} Real c
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (S c)
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ε (d c))))
                      (@Eq.{1} Real (F (X c))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                (S c) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ε (d c)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                            (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_1} ι (H c))))))))))))
          (∀ (c' : Real),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c' →
              @Eq.{1} Real
                  (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
                    @Min.min.{0} Real Real.instMin (a l)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (v l) c'))
                  ε →
                @Eq.{1} Real c' c))
    Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration.{u_1})

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"probe_threshold_optimization\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.probe_threshold_optimization, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.arena.{u_1}
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] (a : ι → Real)
    (_ha :
      ∀ (l : ι),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (a l))
    (_hsum :
      @Eq.{1} Real (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) => a l)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (ε : Real)
    (_hε0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (_hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
    have v : ι → Real := fun (l : ι) => Real.sqrt (a l);
    have F : (ι → Real) → Real := fun (x : ι → Real) =>
      @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (v l) (x l))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
          (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
            @HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (x l)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))));
    have X : Real → ι → Real := fun (c : Real) (l : ι) =>
      @Min.min.{0} Real Real.instMin (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c (v l));
    have H : Real → Finset.{u_1} ι := fun (c : Real) =>
      @Finset.filter.{u_1} ι
        (fun (l : ι) =>
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c (v l)))
        (fun (a : ι) =>
          Real.decidableLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c (v a)))
        (@Finset.univ.{u_1} ι inst);
    have d : Real → Real := fun (c : Real) =>
      @Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid
        (@Finset.filter.{u_1} ι
          (fun (l : ι) =>
            Not
              (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) (H c) l))
          (fun (a : ι) =>
            @instDecidableNot
              (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) (H c) a)
              (@Finset.decidableMem.{u_1} ι (fun (a b : ι) => Classical.propDecidable (@Eq.{u_1 + 1} ι a b)) a (H c)))
          (@Finset.univ.{u_1} ι inst))
        fun (l : ι) => a l;
    have S : Real → Real := fun (c : Real) =>
      @Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (H c) fun (l : ι) => v l;
    @Exists.{1} Real fun (c : Real) =>
      And
        (And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
          (And
            (@Eq.{1} Real
              (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
                @Min.min.{0} Real Real.instMin (a l)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (v l) c))
              ε)
            (And
              (∀ (l : ι),
                And
                  (@LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (X c l))
                  (@LE.le.{0} Real Real.instLE (X c l)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (And
                (∀ (x : ι → Real),
                  (∀ (l : ι),
                      And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (x l))
                        (@LE.le.{0} Real Real.instLE (x l)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                    @LE.le.{0} Real Real.instLE (F x) (F (X c)))
                (And (@LT.lt.{0} Real Real.instLT (d c) ε)
                  (And
                    (@Eq.{1} Real c
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (S c)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ε (d c))))
                    (@Eq.{1} Real (F (X c))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (S c) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ε (d c)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_1} ι (H c))))))))))))
        (∀ (c' : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c' →
            @Eq.{1} Real
                (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) =>
                  @Min.min.{0} Real Real.instMin (a l)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (v l) c'))
                ε →
              @Eq.{1} Real c' c))
  Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration.{u_1})

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.observation0.{u_1} : {ι : Type u_1} →
  [inst : Fintype.{u_1} ι] →
    (a : ι → Real) →
      (ha :
          ∀ (l : ι),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (a l)) →
        (hsum :
            @Eq.{1} Real
              (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) => a l)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          (ε : Real) →
            (hε0 :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  ε) →
              (hε1 :
                  @LT.lt.{0} Real Real.instLT ε
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                (l : ι) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, 0, 0}
                    Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.signature.{u_1} PUnit.unit.{1}
                    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
                      (fun (ι : Type u_1) => @Sigma.{u_1, 0} (ι → Real) fun (x : ι → Real) => Real) ι
                      (@Sigma.mk.{u_1, 0} (ι → Real) (fun (x : ι → Real) => Real) a ε)) :=
  fun {ι : Type u_1} [Fintype.{u_1} ι] (a : ι → Real)
    (ha :
      ∀ (l : ι),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (a l))
    (hsum :
      @Eq.{1} Real (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (l : ι) => a l)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (ε : Real)
    (hε0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (l : ι) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.signature.{u_1}
    Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (ι : Type u_1) => @Sigma.{u_1, 0} (ι → Real) fun (x : ι → Real) => Real) ι
      (@Sigma.mk.{u_1, 0} (ι → Real) (fun (x : ι → Real) => Real) a ε))
    l

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"probe_threshold_optimization\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letValue\",\"body\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.probe_threshold_optimization, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .letValue, .body], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"probe_threshold_optimization\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.probe_threshold_optimization, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration.{u_1}).actual (Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration.{u_1}).variation.2.choose (Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration.{u_1}).variation.1 (Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"ProbeThresholdOptimization\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization, declaration := `Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
