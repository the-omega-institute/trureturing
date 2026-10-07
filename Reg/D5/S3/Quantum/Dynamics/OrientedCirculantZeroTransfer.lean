import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
open _root_.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State p := ZMod p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.val) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original claim; only the selected source operand is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ (∀ (n : ℕ) [NeZero n], n % 4 = 2 → ∀ C : Finset (ZMod n),
    Oriented C → Connected C → ∀ v : ZMod n,
    ZeroTransfer n C v 0 ∧ ZeroTransfer n C 0 v → Odd (O.readout () n v))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro n _ _ C _ _ v _
  exact ⟨0, rfl⟩

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change (0 : ZMod 2).val ≠ (1 : ZMod 2).val
    decide +kernel

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ v => v.val) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Dynamics") "OrientedCirculantZeroTransfer") "result") "Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer/Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ v => v.val) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, definition := some { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, name := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.claim, path := #["arg"] }, coordinates := #[0], readouts := #[{ path := #["arg", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.observationFact0, `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer


noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.arena
noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.arena
noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.arena) (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration).actual

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.observation0 : (n : Nat) →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) n
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      (C : Finset.{0} (ZMod n)) →
        @D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.Oriented n C →
          @D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.Connected n C →
            (v : ZMod n) →
              And
                  (@D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.ZeroTransfer n inst C v
                    (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (ZMod n)
                        (@MulZeroClass.toZero.{0} (ZMod n)
                          (@instMulZeroClassOfSemiring.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))))
                  (@D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.ZeroTransfer n inst C
                    (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (ZMod n)
                        (@MulZeroClass.toZero.{0} (ZMod n)
                          (@instMulZeroClassOfSemiring.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
                    v) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.signature PUnit.unit.{1} n :=
  fun (n : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n]
    (a :
      @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) n
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (C : Finset.{0} (ZMod n)) (a_1 : @D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.Oriented n C)
    (a_2 : @D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.Connected n C) (v : ZMod n)
    (a_3 :
      And
        (@D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.ZeroTransfer n inst C v
          (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod n)
              (@MulZeroClass.toZero.{0} (ZMod n)
                (@instMulZeroClassOfSemiring.{0} (ZMod n)
                  (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))))
        (@D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.ZeroTransfer n inst C
          (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod n)
              (@MulZeroClass.toZero.{0} (ZMod n)
                (@instMulZeroClassOfSemiring.{0} (ZMod n)
                  (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
          v)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.signature
    Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.actual PUnit.unit.{1} n v

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.claim, part := .value, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration).actual (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration).variation.2.choose (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration).variation.1 (Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"OrientedCirculantZeroTransfer\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, declaration := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
