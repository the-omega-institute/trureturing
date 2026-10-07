import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
open _root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Point
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => vertex n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => vertex (n + 1)) (fun e => nomatch e)

/-- All nine geometric clauses and all three infinite series identities remain in the law.
Only the first vertex in the adjacent-edge squared distance is intervened on. -/
def arena : Arena where
  signature := signature
  Law r :=
    (∀ n,
      regular (vertex n) (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) ∧
      sqDist (r.readout () () n) (vertex (n + 1)) = 8 ∧
      vertex n ≠ faceCenter (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      faceNoncollinear (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      vertex (n + 4) = reflected (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 1)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 2)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 3)) ∧
      ∀ i, (vertex n i + vertex (n + 4) i) / 2 =
        faceCenter (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) i) ∧
    PowerSeries.mk (fun n => scaled n (0 : Fin 3)) =
      (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 -
        66 * PowerSeries.X ^ 4 + 23 * PowerSeries.X ^ 3 +
        9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (1 : Fin 3)) =
      (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 -
        90 * PowerSeries.X ^ 4 + 15 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (2 : Fin 3)) =
      (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 -
        24 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 -
          PowerSeries.X - 1) (-1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have edge := (h.1 0).2.1
  norm_num [rejected, realize, sqDist] at edge

def registration : Registration arena
    ((∀ n,
      regular (vertex n) (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) ∧
      sqDist (vertex n) (vertex (n + 1)) = 8 ∧
      vertex n ≠ faceCenter (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      faceNoncollinear (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      vertex (n + 4) = reflected (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 1)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 2)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 3)) ∧
      ∀ i, (vertex n i + vertex (n + 4) i) / 2 =
        faceCenter (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) i) ∧
    PowerSeries.mk (fun n => scaled n (0 : Fin 3)) =
      (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 -
        66 * PowerSeries.X ^ 4 + 23 * PowerSeries.X ^ 3 +
        9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (1 : Fin 3)) =
      (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 -
        90 * PowerSeries.X ^ 4 + 15 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (2 : Fin 3)) =
      (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 -
        24 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 -
          PowerSeries.X - 1) (-1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    have edge := (_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result.1 0).2.1
    change vertex 0 = vertex 1 at h
    simp only [Nat.zero_add, h, sqDist, sub_self, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] at edge
    norm_num at edge

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => vertex n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Recurrence") "BoerdijkCoxeterGeneratingFunctions") "result") "Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions/Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => vertex n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaFact, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceBridgeFact, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observationFact0, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions


noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
    (And
      (∀ (n : Nat),
        And
          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.regular
            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (And
            (@Eq.{1} Rat
              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.sqDist
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Rat (nat_lit 8) (@Rat.instOfNat (nat_lit 8))))
            (And
              (@Ne.{1} D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.Point
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceCenter
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
              (And
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceNoncollinear
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (And
                  (@Eq.{1} D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.Point
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.reflected
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                  (And
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceOrthogonal
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (And
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceOrthogonal
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      (And
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceOrthogonal
                          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
                          @Eq.{1} Rat
                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                              (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n i)
                                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  i))
                              (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceCenter
                              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              i))))))))))
      (And
        (@Eq.{1} (PowerSeries.{0} Rat)
          (@PowerSeries.mk.{0} Rat fun (n : Nat) =>
            D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.scaled n
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0))))
          (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
            (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
            (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHSub.{0} (PowerSeries.{0} Rat)
                (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                  (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                    (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
              (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHAdd.{0} (PowerSeries.{0} Rat)
                  (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                    (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHSub.{0} (PowerSeries.{0} Rat)
                        (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                          (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                      (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHSub.{0} (PowerSeries.{0} Rat)
                          (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                            (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                        (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                          (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                          (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                            (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                              (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 53) (instOfNatNat (nat_lit 53)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))))))
                          (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                            (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                              (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                  (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                            (@PowerSeries.X.{0} Rat Rat.semiring)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                        (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                          (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                          (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                            (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                              (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))))))
                          (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                            (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                              (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                  (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                            (@PowerSeries.X.{0} Rat Rat.semiring)
                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 66)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 66)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 23)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 23)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                    (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                      (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                        (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                          (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                            (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@PowerSeries.X.{0} Rat Rat.semiring))
              (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
            (@PowerSeries.invOfUnit.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                  (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                    (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                      (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                        (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                  (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHSub.{0} (PowerSeries.{0} Rat)
                      (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                        (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@PowerSeries.X.{0} Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                      (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                    (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring)))))
              (@OfNat.ofNat.{0}
                (@Units.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                (nat_lit 1)
                (@One.toOfNat1.{0}
                  (@Units.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                  (@Units.instOne.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))))))))
        (And
          (@Eq.{1} (PowerSeries.{0} Rat)
            (@PowerSeries.mk.{0} Rat fun (n : Nat) =>
              D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.scaled n
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1))))
            (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
              (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHSub.{0} (PowerSeries.{0} Rat)
                  (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                    (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHAdd.{0} (PowerSeries.{0} Rat)
                        (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                          (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                      (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHSub.{0} (PowerSeries.{0} Rat)
                          (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                            (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                        (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                          (@instHAdd.{0} (PowerSeries.{0} Rat)
                            (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                              (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                          (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                            (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                            (@Neg.neg.{0} (PowerSeries.{0} Rat)
                              (@NegZeroClass.toNeg.{0} (PowerSeries.{0} Rat)
                                (@SubNegZeroMonoid.toNegZeroClass.{0} (PowerSeries.{0} Rat)
                                  (@SubtractionMonoid.toSubNegZeroMonoid.{0} (PowerSeries.{0} Rat)
                                    (@SubtractionCommMonoid.toSubtractionMonoid.{0} (PowerSeries.{0} Rat)
                                      (@AddCommGroup.toDivisionAddCommMonoid.{0} (PowerSeries.{0} Rat)
                                        (@MvPowerSeries.instAddCommGroup.{0, 0} Unit Rat Rat.addCommGroup))))))
                              (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                                (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                                  (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                    (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 53) (instOfNatNat (nat_lit 53)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))))))))
                            (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                              (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                                (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                  (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                    (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                              (@PowerSeries.X.{0} Rat Rat.semiring)
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                          (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                            (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                            (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                              (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                                (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))))))
                            (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                              (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                                (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                  (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                    (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                              (@PowerSeries.X.{0} Rat Rat.semiring)
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                        (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                          (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                          (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 90)
                            (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 90)
                              (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 89) (instOfNatNat (nat_lit 89)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88)))))))
                          (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                            (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                              (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                  (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                            (@PowerSeries.X.{0} Rat Rat.semiring)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 15)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 15)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (@PowerSeries.X.{0} Rat Rat.semiring)))
                (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                  (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
              (@PowerSeries.invOfUnit.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                  (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                    (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                      (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                        (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                          (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                    (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHSub.{0} (PowerSeries.{0} Rat)
                        (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                          (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@PowerSeries.X.{0} Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                        (@One.toOfNat1.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHAdd.{0} (PowerSeries.{0} Rat)
                        (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                          (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                      (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring)))))
                (@OfNat.ofNat.{0}
                  (@Units.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                  (nat_lit 1)
                  (@One.toOfNat1.{0}
                    (@Units.{0} Rat
                      (@Semiring.toMonoid.{0} Rat
                        (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                    (@Units.instOne.{0} Rat
                      (@Semiring.toMonoid.{0} Rat
                        (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))))))))
          (@Eq.{1} (PowerSeries.{0} Rat)
            (@PowerSeries.mk.{0} Rat fun (n : Nat) =>
              D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.scaled n
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 2))))
            (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
              (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHAdd.{0} (PowerSeries.{0} Rat)
                  (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                    (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHSub.{0} (PowerSeries.{0} Rat)
                    (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                      (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                  (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHSub.{0} (PowerSeries.{0} Rat)
                      (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                        (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                    (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHAdd.{0} (PowerSeries.{0} Rat)
                        (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                          (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 18)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 18)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 26)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 26)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 24)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 24)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 5)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 5)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                      (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                        (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                          (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                            (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                  (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
              (@PowerSeries.invOfUnit.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHSub.{0} (PowerSeries.{0} Rat)
                    (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                      (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                  (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHSub.{0} (PowerSeries.{0} Rat)
                      (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                        (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                    (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHAdd.{0} (PowerSeries.{0} Rat)
                        (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                          (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 27)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 27)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (@PowerSeries.X.{0} Rat Rat.semiring))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                    (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
                (@Neg.neg.{0}
                  (@Units.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                  (@Units.instNeg.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))
                    (@NonUnitalNonAssocRing.toHasDistribNeg.{0} Rat
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Rat
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Rat
                          (@CommRing.toNonUnitalCommRing.{0} Rat Rat.commRing)))))
                  (@OfNat.ofNat.{0}
                    (@Units.{0} Rat
                      (@Semiring.toMonoid.{0} Rat
                        (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                    (nat_lit 1)
                    (@One.toOfNat1.{0}
                      (@Units.{0} Rat
                        (@Semiring.toMonoid.{0} Rat
                          (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                      (@Units.instOne.{0} Rat
                        (@Semiring.toMonoid.{0} Rat
                          (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))))))))))))
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration)

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
  (And
    (∀ (n : Nat),
      And
        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.regular
          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
        (And
          (@Eq.{1} Rat
            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.sqDist
              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@OfNat.ofNat.{0} Rat (nat_lit 8) (@Rat.instOfNat (nat_lit 8))))
          (And
            (@Ne.{1} D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.Point
              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceCenter
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            (And
              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceNoncollinear
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              (And
                (@Eq.{1} D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.Point
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.reflected
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (And
                  (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceOrthogonal
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceOrthogonal
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (And
                      (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceOrthogonal
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n)
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
                        @Eq.{1} Rat
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex n i)
                              (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                i))
                            (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                          (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.faceCenter
                            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.vertex
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            i))))))))))
    (And
      (@Eq.{1} (PowerSeries.{0} Rat)
        (@PowerSeries.mk.{0} Rat fun (n : Nat) =>
          D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.scaled n
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0))))
        (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
          (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
          (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
            (@instHSub.{0} (PowerSeries.{0} Rat)
              (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                  (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
            (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHAdd.{0} (PowerSeries.{0} Rat)
                (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                  (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
              (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHAdd.{0} (PowerSeries.{0} Rat)
                  (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                    (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHSub.{0} (PowerSeries.{0} Rat)
                      (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                        (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                    (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHSub.{0} (PowerSeries.{0} Rat)
                        (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                          (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 53) (instOfNatNat (nat_lit 53)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 66)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 66)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 23)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 23)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21)))))))
                    (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                      (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                        (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                          (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                            (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                    (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                      (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                  (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                    (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                      (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                        (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                          (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                    (@PowerSeries.X.{0} Rat Rat.semiring)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@PowerSeries.X.{0} Rat Rat.semiring))
            (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
              (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
          (@PowerSeries.invOfUnit.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
            (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
              (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                  (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                    (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                      (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHSub.{0} (PowerSeries.{0} Rat)
                    (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                      (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (@PowerSeries.X.{0} Rat Rat.semiring))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                    (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHAdd.{0} (PowerSeries.{0} Rat)
                  (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                    (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                    (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                      (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                        (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                          (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                            (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@PowerSeries.X.{0} Rat Rat.semiring)))
                (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                  (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring)))))
            (@OfNat.ofNat.{0}
              (@Units.{0} Rat
                (@Semiring.toMonoid.{0} Rat
                  (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
              (nat_lit 1)
              (@One.toOfNat1.{0}
                (@Units.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                (@Units.instOne.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))))))))
      (And
        (@Eq.{1} (PowerSeries.{0} Rat)
          (@PowerSeries.mk.{0} Rat fun (n : Nat) =>
            D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.scaled n
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
            (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
            (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHSub.{0} (PowerSeries.{0} Rat)
                (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                  (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                    (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
              (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHAdd.{0} (PowerSeries.{0} Rat)
                  (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                    (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHSub.{0} (PowerSeries.{0} Rat)
                        (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                          (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                      (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHAdd.{0} (PowerSeries.{0} Rat)
                          (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                            (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                        (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                          (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                          (@Neg.neg.{0} (PowerSeries.{0} Rat)
                            (@NegZeroClass.toNeg.{0} (PowerSeries.{0} Rat)
                              (@SubNegZeroMonoid.toNegZeroClass.{0} (PowerSeries.{0} Rat)
                                (@SubtractionMonoid.toSubNegZeroMonoid.{0} (PowerSeries.{0} Rat)
                                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} (PowerSeries.{0} Rat)
                                    (@AddCommGroup.toDivisionAddCommMonoid.{0} (PowerSeries.{0} Rat)
                                      (@MvPowerSeries.instAddCommGroup.{0, 0} Unit Rat Rat.addCommGroup))))))
                            (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                              (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 54)
                                (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 53) (instOfNatNat (nat_lit 53)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))))))))
                          (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                            (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                              (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                  (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                            (@PowerSeries.X.{0} Rat Rat.semiring)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                        (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                          (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                          (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                            (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 84)
                              (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))))))
                          (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                            (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                              (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                                (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                  (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                            (@PowerSeries.X.{0} Rat Rat.semiring)
                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                      (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                        (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                        (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 90)
                          (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 90)
                            (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 89) (instOfNatNat (nat_lit 89)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88)))))))
                        (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                          (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                            (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                              (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                                (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                  (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                          (@PowerSeries.X.{0} Rat Rat.semiring)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 15)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 15)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                      (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                        (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                          (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                            (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                      (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@PowerSeries.X.{0} Rat Rat.semiring)))
              (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
            (@PowerSeries.invOfUnit.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                  (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                    (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                      (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                        (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                  (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHSub.{0} (PowerSeries.{0} Rat)
                      (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                        (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@PowerSeries.X.{0} Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                      (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHAdd.{0} (PowerSeries.{0} Rat)
                    (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                      (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 9)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 4)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                    (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring)))))
              (@OfNat.ofNat.{0}
                (@Units.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                (nat_lit 1)
                (@One.toOfNat1.{0}
                  (@Units.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                  (@Units.instOne.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))))))))
        (@Eq.{1} (PowerSeries.{0} Rat)
          (@PowerSeries.mk.{0} Rat fun (n : Nat) =>
            D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.scaled n
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 2))))
          (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
            (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
            (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
              (@instHAdd.{0} (PowerSeries.{0} Rat)
                (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                  (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                    (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
              (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHSub.{0} (PowerSeries.{0} Rat)
                  (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                    (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHSub.{0} (PowerSeries.{0} Rat)
                    (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                      (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 18)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 18)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 26)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 26)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                  (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                    (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 24)
                      (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 24)
                        (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))
                    (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                      (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                        (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                          (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                            (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                              (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                      (@PowerSeries.X.{0} Rat Rat.semiring)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                  (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 5)
                    (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 5)
                      (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                  (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                    (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                      (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                        (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                          (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                    (@PowerSeries.X.{0} Rat Rat.semiring)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
            (@PowerSeries.invOfUnit.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                (@instHSub.{0} (PowerSeries.{0} Rat)
                  (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                    (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                      (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                (@HSub.hSub.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                  (@instHSub.{0} (PowerSeries.{0} Rat)
                    (@SubNegMonoid.toSub.{0} (PowerSeries.{0} Rat)
                      (@AddGroup.toSubNegMonoid.{0} (PowerSeries.{0} Rat)
                        (@MvPowerSeries.instAddGroup.{0, 0} Unit Rat Rat.addGroup))))
                  (@HAdd.hAdd.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                    (@instHAdd.{0} (PowerSeries.{0} Rat)
                      (@Distrib.toAdd.{0} (PowerSeries.{0} Rat)
                        (@instDistribOfSemiring.{0} (PowerSeries.{0} Rat)
                          (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 27)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 27)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@HMul.hMul.{0, 0, 0} (PowerSeries.{0} Rat) (PowerSeries.{0} Rat) (PowerSeries.{0} Rat)
                      (@instHMul.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instMul.{0, 0} Unit Rat Rat.semiring))
                      (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} (PowerSeries.{0} Rat) (nat_lit 3)
                          (@AddMonoidWithOne.toNatCast.{0} (PowerSeries.{0} Rat)
                            (@MvPowerSeries.instAddMonoidWithOne.{0, 0} Unit Rat Rat.semiring))
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@HPow.hPow.{0, 0, 0} (PowerSeries.{0} Rat) Nat (PowerSeries.{0} Rat)
                        (@instHPow.{0, 0} (PowerSeries.{0} Rat) Nat
                          (@NPow.toPow.{0} (PowerSeries.{0} Rat)
                            (@Monoid.toNPow.{0} (PowerSeries.{0} Rat)
                              (@Semiring.toMonoid.{0} (PowerSeries.{0} Rat)
                                (@MvPowerSeries.instSemiring.{0, 0} Unit Rat Rat.semiring)))))
                        (@PowerSeries.X.{0} Rat Rat.semiring)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  (@PowerSeries.X.{0} Rat Rat.semiring))
                (@OfNat.ofNat.{0} (PowerSeries.{0} Rat) (nat_lit 1)
                  (@One.toOfNat1.{0} (PowerSeries.{0} Rat) (@MvPowerSeries.instOne.{0, 0} Unit Rat Rat.semiring))))
              (@Neg.neg.{0}
                (@Units.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                (@Units.instNeg.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))
                  (@NonUnitalNonAssocRing.toHasDistribNeg.{0} Rat
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Rat
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Rat
                        (@CommRing.toNonUnitalCommRing.{0} Rat Rat.commRing)))))
                (@OfNat.ofNat.{0}
                  (@Units.{0} Rat
                    (@Semiring.toMonoid.{0} Rat
                      (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                  (nat_lit 1)
                  (@One.toOfNat1.{0}
                    (@Units.{0} Rat
                      (@Semiring.toMonoid.{0} Rat
                        (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing))))
                    (@Units.instOne.{0} Rat
                      (@Semiring.toMonoid.{0} Rat
                        (@Ring.toSemiring.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)))))))))))))
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration)

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observation0 : (n : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.signature
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"result\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [.function, .argument, .body, .argument, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).actual (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).variation.2.choose (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).variation.1 (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
