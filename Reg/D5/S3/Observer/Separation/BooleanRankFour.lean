import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanRankFour
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.BooleanRankFour

open _root_.D5.S3.Observer.Separation.BooleanRankFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The entire source conjunction; only the left budget's selected occurrence varies. -/
def arena : Arena where
  signature := signature
  Law R :=
    ActiveConnected F4 ∧ cycleRank F4 = 4 ∧
    (leftConflict F4).chromaticNumber = 2 ∧
    (rightConflict F4).chromaticNumber = 2 ∧
    (∀ p q, Admits F4 (R.readout () () p) q ↔ Region p q) ∧
    (∀ s : ℤ, 4 ≤ s → ∀ p q, Uniform s p q ↔ Region p q)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have admits : Admits F4 0 4 := (h.2.2.2.2.1 2 4).mpr (by norm_num [Region])
  have region : Region 0 4 := (result.2.2.2.2.1 0 4).mp admits
  norm_num [Region] at region

def registration : Registration arena
    (ActiveConnected F4 ∧ cycleRank F4 = 4 ∧
    (leftConflict F4).chromaticNumber = 2 ∧
    (rightConflict F4).chromaticNumber = 2 ∧
    (∀ p q, Admits F4 p q ↔ Region p q) ∧
    (∀ s : ℤ, 4 ≤ s → ∀ p q, Uniform s p q ↔ Region p q)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Separation.BooleanRankFour.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ p => p) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "BooleanRankFour") "result") "Reg.D5.S3.Observer.Separation.BooleanRankFour/Reg.D5.S3.Observer.Separation.BooleanRankFour.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ p => p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.BooleanRankFour, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Separation.BooleanRankFour, declaration := `D5.S3.Observer.Separation.BooleanRankFour.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.observationFact0, `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Observer.Separation.BooleanRankFour


noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanRankFour.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanRankFour.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.BooleanRankFour.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankFour.arena
    (And
      (@D5.S3.Observer.Separation.BooleanRankFour.ActiveConnected
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        D5.S3.Observer.Separation.BooleanRankFour.F4)
      (And
        (@Eq.{1} Int
          (@D5.S3.Observer.Separation.BooleanRankFour.cycleRank
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            D5.S3.Observer.Separation.BooleanRankFour.F4)
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
        (And
          (@Eq.{1} ENat
            (@SimpleGraph.chromaticNumber.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@D5.S3.Observer.Separation.BooleanRankFour.leftConflict
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                D5.S3.Observer.Separation.BooleanRankFour.F4))
            (@OfNat.ofNat.{0} ENat (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENat (nat_lit 2) ENat.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (And
            (@Eq.{1} ENat
              (@SimpleGraph.chromaticNumber.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (@D5.S3.Observer.Separation.BooleanRankFour.rightConflict
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  D5.S3.Observer.Separation.BooleanRankFour.F4))
              (@OfNat.ofNat.{0} ENat (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} ENat (nat_lit 2) ENat.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (And
              (∀ (p q : Nat),
                Iff
                  (@D5.S3.Observer.Separation.BooleanRankFour.Admits
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    D5.S3.Observer.Separation.BooleanRankFour.F4 p q)
                  (D5.S3.Observer.Separation.BooleanRankFour.Region p q))
              (∀ (s : Int),
                @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) s →
                  ∀ (p q : Nat),
                    Iff (D5.S3.Observer.Separation.BooleanRankFour.Uniform s p q)
                      (D5.S3.Observer.Separation.BooleanRankFour.Region p q)))))))
    Reg.D5.S3.Observer.Separation.BooleanRankFour.registration)

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanRankFour, declaration := `D5.S3.Observer.Separation.BooleanRankFour.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.BooleanRankFour.arena
  (And
    (@D5.S3.Observer.Separation.BooleanRankFour.ActiveConnected
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) D5.S3.Observer.Separation.BooleanRankFour.F4)
    (And
      (@Eq.{1} Int
        (@D5.S3.Observer.Separation.BooleanRankFour.cycleRank
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          D5.S3.Observer.Separation.BooleanRankFour.F4)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
      (And
        (@Eq.{1} ENat
          (@SimpleGraph.chromaticNumber.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@D5.S3.Observer.Separation.BooleanRankFour.leftConflict
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              D5.S3.Observer.Separation.BooleanRankFour.F4))
          (@OfNat.ofNat.{0} ENat (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} ENat (nat_lit 2) ENat.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (And
          (@Eq.{1} ENat
            (@SimpleGraph.chromaticNumber.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (@D5.S3.Observer.Separation.BooleanRankFour.rightConflict
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                D5.S3.Observer.Separation.BooleanRankFour.F4))
            (@OfNat.ofNat.{0} ENat (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENat (nat_lit 2) ENat.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (And
            (∀ (p q : Nat),
              Iff
                (@D5.S3.Observer.Separation.BooleanRankFour.Admits
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  D5.S3.Observer.Separation.BooleanRankFour.F4 p q)
                (D5.S3.Observer.Separation.BooleanRankFour.Region p q))
            (∀ (s : Int),
              @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) s →
                ∀ (p q : Nat),
                  Iff (D5.S3.Observer.Separation.BooleanRankFour.Uniform s p q)
                    (D5.S3.Observer.Separation.BooleanRankFour.Region p q)))))))
  Reg.D5.S3.Observer.Separation.BooleanRankFour.registration)

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.observation0 : (p q : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankFour.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (p q : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankFour.signature Reg.D5.S3.Observer.Separation.BooleanRankFour.actual
    PUnit.unit.{1} PUnit.unit.{1} p

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanRankFour, declaration := `D5.S3.Observer.Separation.BooleanRankFour.result, part := .type, path := [.argument, .argument, .argument, .argument, .function, .argument, .body, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Separation.BooleanRankFour, declaration := `D5.S3.Observer.Separation.BooleanRankFour.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Separation.BooleanRankFour.registration).actual (Reg.D5.S3.Observer.Separation.BooleanRankFour.registration).variation.2.choose (Reg.D5.S3.Observer.Separation.BooleanRankFour.registration).variation.1 (Reg.D5.S3.Observer.Separation.BooleanRankFour.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankFour\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankFour, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankFour.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
