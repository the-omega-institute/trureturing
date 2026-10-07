import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Permutations.MamedeDeletionEquiv
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeDeletionEquiv
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv

-- A nonoscillating source with i = j and empty outer words witnesses nonvacuity.
private theorem sample_reduced : reducedWord 3 [2, 1, 2, 3, 2] := by
  refine ⟨by simp [validWord], ?_⟩
  intro v hv hp
  by_contra hn
  have hl : v.length ≤ 4 := by simp only [List.length_cons, List.length_nil] at hn; omega
  rcases v with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
  · revert hp; decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    interval_cases a <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    interval_cases a <;> interval_cases b <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    obtain ⟨hc0, hc1⟩ := hv c (by simp)
    interval_cases a <;> interval_cases b <;> interval_cases c <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    obtain ⟨hc0, hc1⟩ := hv c (by simp)
    obtain ⟨hd0, hd1⟩ := hv d (by simp)
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      interval_cases d <;> revert hp <;> decide
  · simp only [List.length_cons] at hl
    omega

private theorem sample_hs : exactSourceHypotheses 3 1 3 2 2
    (wordProduct 3 [2, 1, 2, 3, 2]) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · decide
  · exact ⟨[2, 1, 2, 3, 2], ⟨sample_reduced, by simp [consecutive], rfl⟩,
      by simp [oscillation, spikes, internalSpikes, segmentLengths, weakIncreasing]⟩

abbrev signature : Signature where
  Params := Σ _ : Nat, Σ _ : Nat, List Nat
  State _ := List Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => imageWord p.1 p.2.1 p.2.2 q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n m M i j : Nat) (σ : Equiv.Perm (Fin (n + 1)))
      (_hs : exactSourceHypotheses n m M i j σ),
    ∃ e : {a : List Nat // singletonWord n σ a} ≃
        {b : List Nat // singletonWord n
          (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b},
      ∀ (a : {a : List Nat // singletonWord n σ a}) (p q : List Nat),
        sourceShape m M i j a.val p q →
          (e a).val = r.readout () ⟨i, j, p⟩ q ∧
          a.val.length = (e a).val.length + (deletedExcursion m M i).length ∧
          0 < (deletedExcursion m M i).length

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := h 3 1 3 2 2 _ sample_hs
  let a : {w : List Nat // singletonWord 3
      (wordProduct 3 [2, 1, 2, 3, 2]) w} :=
    ⟨[2, 1, 2, 3, 2], sample_reduced, by simp [consecutive], rfl⟩
  have hshape : sourceShape 1 3 2 2 a.val [] [] := by
    exact ⟨rfl, by simp, by simp⟩
  obtain ⟨hword, hlength, _⟩ := he a [] [] hshape
  change (e a).val = [] at hword
  rw [hword] at hlength
  norm_num [a, deletedExcursion, descending, ascending] at hlength

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨⟨2, 2, []⟩, [], [0], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_deletion_equiv, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Permutations.MamedeDeletionEquiv.source_deletion_equiv) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p q => imageWord p.1 p.2.1 p.2.2 q) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Permutations") "MamedeDeletionEquiv") "source_deletion_equiv") "Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv/Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration,
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
    (fun _ p q => imageWord p.1 p.2.1 p.2.2 q) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Permutations.MamedeDeletionEquiv, definition := none, coordinates := #[3, 4, 9], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `D5.S1.Words.Permutations.MamedeDeletionEquiv.source_deletion_equiv, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.observationFact0, `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv


noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena
noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena
noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.actual)
    Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration)

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"source_deletion_equiv\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `D5.S1.Words.Permutations.MamedeDeletionEquiv.source_deletion_equiv, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.arena Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.actual)
  Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration)

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.observation0 : (n m M i j : Nat) →
  (σ :
      Equiv.Perm.{1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    (hs : D5.S1.Words.Permutations.MamedeAdjacentWords.exactSourceHypotheses n m M i j σ) →
      (e :
          Equiv.{1, 1}
            (@Subtype.{1} (List.{0} Nat) fun (a : List.{0} Nat) =>
              D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n σ a)
            (@Subtype.{1} (List.{0} Nat) fun (b : List.{0} Nat) =>
              D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n
                (@HMul.hMul.{0, 0, 0}
                  (Equiv.Perm.{1}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Equiv.Perm.{1}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Equiv.Perm.{1}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@instHMul.{0}
                    (Equiv.Perm.{1}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@Equiv.Perm.instMul.{0}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  σ
                  (@Inv.inv.{0}
                    (Equiv.Perm.{1}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@Equiv.Perm.instInv.{0}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (D5.S1.Words.Permutations.MamedeAdjacentWords.wordProduct n
                      (D5.S1.Words.Permutations.MamedeAdjacentWords.deletedExcursion m M i))))
                b)) →
        (a :
            @Subtype.{1} (List.{0} Nat) fun (a : List.{0} Nat) =>
              D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n σ a) →
          (p q : List.{0} Nat) →
            D5.S1.Words.Permutations.MamedeAdjacentWords.sourceShape m M i j
                (@Subtype.val.{1} (List.{0} Nat)
                  (fun (a : List.{0} Nat) => D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n σ a) a)
                p q →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) i
                  (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) j p)) :=
  fun (n m M i j : Nat)
    (σ :
      Equiv.Perm.{1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (hs : D5.S1.Words.Permutations.MamedeAdjacentWords.exactSourceHypotheses n m M i j σ)
    (e :
      Equiv.{1, 1}
        (@Subtype.{1} (List.{0} Nat) fun (a : List.{0} Nat) =>
          D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n σ a)
        (@Subtype.{1} (List.{0} Nat) fun (b : List.{0} Nat) =>
          D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n
            (@HMul.hMul.{0, 0, 0}
              (Equiv.Perm.{1}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Equiv.Perm.{1}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Equiv.Perm.{1}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@instHMul.{0}
                (Equiv.Perm.{1}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Equiv.Perm.instMul.{0}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              σ
              (@Inv.inv.{0}
                (Equiv.Perm.{1}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Equiv.Perm.instInv.{0}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (D5.S1.Words.Permutations.MamedeAdjacentWords.wordProduct n
                  (D5.S1.Words.Permutations.MamedeAdjacentWords.deletedExcursion m M i))))
            b))
    (a :
      @Subtype.{1} (List.{0} Nat) fun (a : List.{0} Nat) =>
        D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n σ a)
    (p q : List.{0} Nat)
    (a_1 :
      D5.S1.Words.Permutations.MamedeAdjacentWords.sourceShape m M i j
        (@Subtype.val.{1} (List.{0} Nat)
          (fun (a : List.{0} Nat) => D5.S1.Words.Permutations.MamedeAdjacentWords.singletonWord n σ a) a)
        p q) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.signature Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.actual
    PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) i
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) j p))
    q

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"source_deletion_equiv\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `D5.S1.Words.Permutations.MamedeDeletionEquiv.source_deletion_equiv, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"source_deletion_equiv\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `D5.S1.Words.Permutations.MamedeDeletionEquiv.source_deletion_equiv, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration).actual (Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration).variation.2.choose (Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration).variation.1 (Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Permutations\",\"MamedeDeletionEquiv\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv, declaration := `Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
