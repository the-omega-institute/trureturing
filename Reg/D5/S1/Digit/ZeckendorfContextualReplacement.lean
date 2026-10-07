import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfContextualReplacement
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Conventions
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfContextualReplacement
open D5.S1.Digit.GoldenBase4IntervalMachine

namespace Reg.D5.S1.Digit.ZeckendorfContextualReplacement
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ H : ℕ, List (Fin 2)
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Fin 2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p u => residual (Nat.fib p.1) (p.2 ++ B1 ++ u)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ) (p u : List (Fin 2)), 14 ≤ H → 14 + u.length ≤ H →
    NoAdjacentOnes (p ++ B1 ++ u) →
    R.readout () ⟨H, p⟩ u = residual (Nat.fib H) (p ++ B0 ++ u)

def rejected : Realization signature := realize signature
  (fun _ _ _ => fun _ => some false) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 14 [] [] (by norm_num) (by norm_num)
    (by norm_num [NoAdjacentOnes, List.isChain_cons_cons, B1])
  have hv : value B0 = 196 := by
    norm_num [value, fibPair, Nat.fib, B0]
  have hw : wdigits 573 = [14, 12, 9, 7, 5] := by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]
  have hres : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B0 [] = some true := by
    simp only [D5.S1.Digit.ZeckendorfRawWindow.residual, List.append_nil, parity]
    rw [show Nat.fib 14 = 377 by norm_num, hv, hw]
    norm_num [B0, NoAdjacentOnes, List.isChain_cons_cons, value, fibPair]
  have hthis := congrFun hh []
  have hfalse : (some false : Option Bool) =
      D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B0 [] := by
    simpa [rejected, realize, List.append_nil] using hthis
  rw [hres] at hfalse
  cases hfalse

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨contextual_replacement, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨14, []⟩, [], [0], ?_⟩
    intro he
    have hh := congrFun he []
    have hv0 : value B1 = 225 := by
      norm_num [value, fibPair, Nat.fib, B1]
    have hv1 : value (B1 ++ [0]) = 364 := by
      norm_num [value, fibPair, Nat.fib, B1]
    have hw0 : wdigits 602 = [14, 12, 10, 8, 5] := by
      symm
      apply wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    have hw1 : wdigits 741 = [15, 11, 9, 6] := by
      symm
      apply wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    have h0 : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B1 [] = some true := by
      simp only [D5.S1.Digit.ZeckendorfRawWindow.residual, List.append_nil, parity]
      rw [show Nat.fib 14 = 377 by norm_num, hv0, hw0]
      norm_num [B1, NoAdjacentOnes, List.isChain_cons_cons, value, fibPair]
    have h1 : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) (B1 ++ [0]) [] = some false := by
      simp only [D5.S1.Digit.ZeckendorfRawWindow.residual, List.append_nil, parity]
      rw [show Nat.fib 14 = 377 by norm_num, hv1, hw1]
      norm_num [B1, NoAdjacentOnes, List.isChain_cons_cons, value, fibPair]
    have hh' : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B1 [] =
        D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) (B1 ++ [0]) [] := by
      simpa [actual, realize, List.append_nil, List.nil_append] using hh
    rw [h0, h1] at hh'
    cases hh'

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfContextualReplacement.contextual_replacement) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p u => residual (Nat.fib p.1) (p.2 ++ B1 ++ u)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfContextualReplacement") "contextual_replacement") "Reg.D5.S1.Digit.ZeckendorfContextualReplacement/Reg.D5.S1.Digit.ZeckendorfContextualReplacement.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration,
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
    (fun _ p u => residual (Nat.fib p.1) (p.2 ++ B1 ++ u)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfContextualReplacement, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `D5.S1.Digit.ZeckendorfContextualReplacement.contextual_replacement, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.observationFact0, `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfContextualReplacement


noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfContextualReplacement.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfContextualReplacement.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.arena) (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration).actual

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"contextual_replacement\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `D5.S1.Digit.ZeckendorfContextualReplacement.contextual_replacement, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration).bridge

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.observation0 : (H : Nat) →
  (p u : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) H) →
      (huH :
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
              (@List.length.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) u))
            H) →
        (hlegal :
            D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes
              (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@instHAppendOfAppend.{0} (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@List.instAppend.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@HAppend.hAppend.{0, 0, 0}
                  (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@instHAppendOfAppend.{0}
                    (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@List.instAppend.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  p D5.S1.Digit.ZeckendorfContextualReplacement.B1)
                u)) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S1.Digit.ZeckendorfContextualReplacement.signature PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat
              (fun (H : Nat) => List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) H p) :=
  fun (H : Nat) (p u : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) H)
    (huH :
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
          (@List.length.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) u))
        H)
    (hlegal :
      D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@instHAppendOfAppend.{0} (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@List.instAppend.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@instHAppendOfAppend.{0} (List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@List.instAppend.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            p D5.S1.Digit.ZeckendorfContextualReplacement.B1)
          u)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfContextualReplacement.signature Reg.D5.S1.Digit.ZeckendorfContextualReplacement.actual
    PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (H : Nat) => List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) H p)
    u

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"contextual_replacement\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `D5.S1.Digit.ZeckendorfContextualReplacement.contextual_replacement, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"contextual_replacement\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `D5.S1.Digit.ZeckendorfContextualReplacement.contextual_replacement, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration).actual (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration).variation.1 (Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfContextualReplacement\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement, declaration := `Reg.D5.S1.Digit.ZeckendorfContextualReplacement.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
