import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Erdos699JointAdjacentCores
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Erdos699JointAdjacentCores
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Erdos699JointAdjacentCores

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law := fun r => ∀ (B s : ℤ),
    5 ≤ B → Odd B → 1 ≤ s → s ≤ B - 1 →
    2 * B + 1 ∣ 4 * s ^ 2 - 1 →
    B ∣ (s - 1) * s * (s + 1) →
    1 < Int.gcd B (s - 1) ∧
    1 < Int.gcd B s ∧
    1 < Int.gcd B (r.readout () () s)

def actual : Realization signature :=
  realize signature (fun _ _ s => s + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := (h 38335 11561
    (by norm_num) (by norm_num [Odd]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2.2
  change (1 : ℕ) < Int.gcd 38335 1 at hfalse
  norm_num at hfalse

def registration : Registration arena
    (∀ (B s : ℤ), 5 ≤ B → Odd B → 1 ≤ s → s ≤ B - 1 →
      2 * B + 1 ∣ 4 * s ^ 2 - 1 →
      B ∣ (s - 1) * s * (s + 1) →
      1 < Int.gcd B (s - 1) ∧
      1 < Int.gcd B s ∧
      1 < Int.gcd B (s + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨erdos699_joint_adjacent_gcds, rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℤ), (1 : ℤ), ?_⟩
    change (0 : ℤ) + 1 ≠ 1 + 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ s => s + 1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Erdos699JointAdjacentCores") "erdos699_joint_adjacent_gcds") "Reg.D5.S3.Arith.Erdos699JointAdjacentCores/Reg.D5.S3.Arith.Erdos699JointAdjacentCores.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ s => s + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Erdos699JointAdjacentCores, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `D5.S3.Arith.Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.observationFact0, `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699JointAdjacentCores


noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Erdos699JointAdjacentCores.arena
noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Erdos699JointAdjacentCores.arena
noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.arena) (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration).actual

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"erdos699_joint_adjacent_gcds\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `D5.S3.Arith.Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration).bridge

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.observation0 : (B s : Int) →
  (hB : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))) B) →
    (hodd : @Odd.{0} Int Int.instSemiring B) →
      (hs : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) s) →
        (hsB :
            @LE.le.{0} Int Int.instLEInt s
              (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) B
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
          (hquad :
              @Dvd.dvd.{0} Int Int.instDvd
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) B)
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) s
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
            (hcubic :
                @Dvd.dvd.{0} Int Int.instDvd B
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) s
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      s)
                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Arith.Erdos699JointAdjacentCores.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (B s : Int) (hB : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))) B)
    (hodd : @Odd.{0} Int Int.instSemiring B)
    (hs : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) s)
    (hsB :
      @LE.le.{0} Int Int.instLEInt s
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) B
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
    (hquad :
      @Dvd.dvd.{0} Int Int.instDvd
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) B)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) s
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
    (hcubic :
      @Dvd.dvd.{0} Int Int.instDvd B
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) s
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            s)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Erdos699JointAdjacentCores.signature Reg.D5.S3.Arith.Erdos699JointAdjacentCores.actual
    PUnit.unit.{1} PUnit.unit.{1} s

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"erdos699_joint_adjacent_gcds\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `D5.S3.Arith.Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"erdos699_joint_adjacent_gcds\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `D5.S3.Arith.Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration).actual (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration).variation.2.choose (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration).variation.1 (Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699JointAdjacentCores\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
