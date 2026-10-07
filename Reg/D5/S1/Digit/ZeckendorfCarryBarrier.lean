import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfCarryBarrier
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.ZeckendorfCarryBarrier
open D5.S0.Conventions

namespace Reg.D5.S1.Digit.ZeckendorfCarryBarrier
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ P : List ℕ, Σ m : ℕ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ k => k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : List ℕ) (m j : ℕ), P.IsZeckendorfRep → 4 ≤ m →
    (∀ k ∈ P, m ≤ k) → m - 1 ≤ j →
    ∀ k ∈ wdigits ((P.map Nat.fib).sum + Nat.fib j), m - 2 ≤
      R.readout () ⟨P, ⟨m, j⟩⟩ k

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [] 4 3 (by simp [List.IsZeckendorfRep]) (by omega) (by simp) (by omega)
  have hwd : wdigits (Nat.fib 3) = [3] := by
    norm_num [Nat.fib]
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]
  change ∀ k ∈ wdigits (Nat.fib 3), 4 - 2 ≤ rejected.readout () ⟨[], ⟨4, 3⟩⟩ k at hh
  rw [hwd] at hh
  have := hh 3 (by simp)
  simp [rejected, realize] at this

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lower_support_carry_barrier, rejected, rejected_law⟩
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
    refine ⟨⟨[], ⟨4, 3⟩⟩, 0, 1, ?_⟩
    simp [actual, realize]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfCarryBarrier.lower_support_carry_barrier) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ k => k) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfCarryBarrier") "lower_support_carry_barrier") "Reg.D5.S1.Digit.ZeckendorfCarryBarrier/Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ k => k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfCarryBarrier, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `D5.S1.Digit.ZeckendorfCarryBarrier.lower_support_carry_barrier, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.observationFact0, `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfCarryBarrier


noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena Reg.D5.S1.Digit.ZeckendorfCarryBarrier.actual)
    Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration)

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"lower_support_carry_barrier\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `D5.S1.Digit.ZeckendorfCarryBarrier.lower_support_carry_barrier, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfCarryBarrier.arena Reg.D5.S1.Digit.ZeckendorfCarryBarrier.actual)
  Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration)

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.observation0 : (P : List.{0} Nat) →
  (m j : Nat) →
    (hP : List.IsZeckendorfRep P) →
      (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m) →
        (hmin :
            ∀ (k : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) P k →
                @LE.le.{0} Nat instLENat m k) →
          (hj :
              @LE.le.{0} Nat instLENat
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j) →
            (k : Nat) →
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                  (D5.S0.Conventions.wdigits
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
                        (@List.map.{0, 0} Nat Nat Nat.fib P))
                      (Nat.fib j)))
                  k →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S1.Digit.ZeckendorfCarryBarrier.signature PUnit.unit.{1}
                  (@Sigma.mk.{0, 0} (List.{0} Nat) (fun (P : List.{0} Nat) => @Sigma.{0, 0} Nat fun (m : Nat) => Nat) P
                    (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => Nat) m j)) :=
  fun (P : List.{0} Nat) (m j : Nat) (hP : List.IsZeckendorfRep P)
    (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m)
    (hmin :
      ∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) P k → @LE.le.{0} Nat instLENat m k)
    (hj :
      @LE.le.{0} Nat instLENat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        j)
    (k : Nat)
    (a :
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
        (D5.S0.Conventions.wdigits
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
              (@List.map.{0, 0} Nat Nat Nat.fib P))
            (Nat.fib j)))
        k) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfCarryBarrier.signature Reg.D5.S1.Digit.ZeckendorfCarryBarrier.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} (List.{0} Nat) (fun (P : List.{0} Nat) => @Sigma.{0, 0} Nat fun (m : Nat) => Nat) P
      (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => Nat) m j))
    k

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"lower_support_carry_barrier\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `D5.S1.Digit.ZeckendorfCarryBarrier.lower_support_carry_barrier, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"lower_support_carry_barrier\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `D5.S1.Digit.ZeckendorfCarryBarrier.lower_support_carry_barrier, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration).actual (Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration).variation.1 (Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfCarryBarrier\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier, declaration := `Reg.D5.S1.Digit.ZeckendorfCarryBarrier.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
