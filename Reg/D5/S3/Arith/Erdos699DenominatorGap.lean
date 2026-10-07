import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Erdos699DenominatorGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Erdos699DenominatorGap

open _root_.D5.S3.Arith.Erdos699DenominatorGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The only observed state is the original integer `n`; no parameter is hidden
in a coordinate or replaced by an assumption on a restricted state space. -/
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Substitute only the selected conclusion LHS. All seven integer parameters
and all eight assumptions retain the source order and expressions. -/
def arena : Arena where
  signature := signature
  Law := fun r => ∀ (n L R j m D k : ℤ),
    8 ≤ n → 0 < R → 0 < m → 2 * m < L → 0 < D →
    n - 1 = L * R → j = 1 + m * R →
    D * (n - j) * (n - j - 1) = k * (n - 1) * (n - 2) →
    (r.readout () () n : ℤ) < D * L ^ 2

def actual : Realization signature :=
  realize signature (fun _ _ (n : ℤ) => 4 * (n - 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (256 : ℤ)) (fun e => nomatch e)

/-- This tuple satisfies every original hypothesis; the intervention gives
`256 < 256`. Thus the rejection does not depend on inconsistent assumptions. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h 9 8 1 2 1 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (256 : ℤ) < 4 * 8 ^ 2 at hfalse
  norm_num at hfalse

def registration : Registration arena
    (∀ (n L R j m D k : ℤ),
      8 ≤ n → 0 < R → 0 < m → 2 * m < L → 0 < D →
      n - 1 = L * R → j = 1 + m * R →
      D * (n - j) * (n - j - 1) = k * (n - 1) * (n - 2) →
      4 * (n - 2) < D * L ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨erdos699_denominator_gap, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (2 : ℤ), (3 : ℤ), ?_⟩
    change (4 : ℤ) * (2 - 2) ≠ 4 * (3 - 2)
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ (n : ℤ) => 4 * (n - 2)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Erdos699DenominatorGap") "erdos699_denominator_gap") "Reg.D5.S3.Arith.Erdos699DenominatorGap/Reg.D5.S3.Arith.Erdos699DenominatorGap.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ (n : ℤ) => 4 * (n - 2)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Erdos699DenominatorGap, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Erdos699DenominatorGap, declaration := `D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.observationFact0, `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699DenominatorGap


noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Erdos699DenominatorGap.arena
noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Erdos699DenominatorGap.arena
noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Erdos699DenominatorGap.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Erdos699DenominatorGap.arena
    (∀ (n L R j m D k : Int),
      @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8))) n →
        @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) R →
          @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) m →
            @LT.lt.{0} Int Int.instLTInt
                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) m)
                L →
              @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) D →
                @Eq.{1} Int
                    (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) L R) →
                  @Eq.{1} Int j
                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m R)) →
                    @Eq.{1} Int
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) D
                            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j))
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j)
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) k
                            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
                      @LT.lt.{0} Int Int.instLTInt
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) D
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) L
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    Reg.D5.S3.Arith.Erdos699DenominatorGap.registration)

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"erdos699_denominator_gap\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Erdos699DenominatorGap, declaration := `D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Erdos699DenominatorGap.arena
  (∀ (n L R j m D k : Int),
    @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8))) n →
      @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) R →
        @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) m →
          @LT.lt.{0} Int Int.instLTInt
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) m)
              L →
            @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) D →
              @Eq.{1} Int
                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) L R) →
                @Eq.{1} Int j
                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m R)) →
                  @Eq.{1} Int
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) D
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j))
                        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j)
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) k
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
                    @LT.lt.{0} Int Int.instLTInt
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
                        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) D
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  Reg.D5.S3.Arith.Erdos699DenominatorGap.registration)

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.observation0 : (n L R j m D k : Int) →
  (hn : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8))) n) →
    (hR : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) R) →
      (hm : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) m) →
        (hmL :
            @LT.lt.{0} Int Int.instLTInt
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) m)
              L) →
          (hD : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) D) →
            (hnLR :
                @Eq.{1} Int
                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) L R)) →
              (hj :
                  @Eq.{1} Int j
                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m R))) →
                (hint :
                    @Eq.{1} Int
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) D
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j))
                        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j)
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) k
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Arith.Erdos699DenominatorGap.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n L R j m D k : Int)
    (hn : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8))) n)
    (hR : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) R)
    (hm : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) m)
    (hmL :
      @LT.lt.{0} Int Int.instLTInt
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) m)
        L)
    (hD : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) D)
    (hnLR :
      @Eq.{1} Int
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) L R))
    (hj :
      @Eq.{1} Int j
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m R)))
    (hint :
      @Eq.{1} Int
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) D
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j))
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n j)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) k
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) n
            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Erdos699DenominatorGap.signature Reg.D5.S3.Arith.Erdos699DenominatorGap.actual PUnit.unit.{1}
    PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"erdos699_denominator_gap\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Erdos699DenominatorGap, declaration := `D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"erdos699_denominator_gap\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Erdos699DenominatorGap, declaration := `D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Erdos699DenominatorGap.registration).actual (Reg.D5.S3.Arith.Erdos699DenominatorGap.registration).variation.2.choose (Reg.D5.S3.Arith.Erdos699DenominatorGap.registration).variation.1 (Reg.D5.S3.Arith.Erdos699DenominatorGap.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699DenominatorGap\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap, declaration := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
