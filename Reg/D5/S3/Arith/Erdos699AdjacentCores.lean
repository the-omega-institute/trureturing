import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Erdos699AdjacentCores
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Erdos699AdjacentCores

open _root_.D5.S3.Arith.Erdos699AdjacentCores
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law := fun r => ∀ (n M t R₁ R₂ δ₁ δ₂ : ℕ),
    0 < t → 2 * t < M → R₁.Coprime R₂ →
    R₁ ∣ t * (M - t) → R₂ ∣ t * (M - t) * (M - 2 * t) →
    δ₁ ≤ 3 → δ₂ ≤ 3 →
    n = δ₁ * R₁ + 1 → n = 2 * δ₂ * R₂ + 2 →
    r.readout () () n ≤ 3 * M ^ 6

def actual : Realization signature :=
  realize signature (fun _ _ n => ((n - 1) * (n - 2)) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2188) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h 4 3 1 1 1 3 1
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  change (2188 : ℕ) ≤ 3 * 3 ^ 6 at hfalse
  norm_num at hfalse

def registration : Registration arena
    (∀ (n M t R₁ R₂ δ₁ δ₂ : ℕ),
      0 < t → 2 * t < M → R₁.Coprime R₂ →
      R₁ ∣ t * (M - t) → R₂ ∣ t * (M - t) * (M - 2 * t) →
      δ₁ ≤ 3 → δ₂ ≤ 3 →
      n = δ₁ * R₁ + 1 → n = 2 * δ₂ * R₂ + 2 →
      ((n - 1) * (n - 2)) ^ 2 ≤ 3 * M ^ 6) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨adjacent_core_numerator_bound, rejected, rejected_law⟩
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
    refine ⟨(), (4 : ℕ), (5 : ℕ), ?_⟩
    change (((4 - 1) * (4 - 2)) ^ 2 : ℕ) ≠ ((5 - 1) * (5 - 2)) ^ 2
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Erdos699AdjacentCores.adjacent_core_numerator_bound) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ n => ((n - 1) * (n - 2)) ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Erdos699AdjacentCores") "adjacent_core_numerator_bound") "Reg.D5.S3.Arith.Erdos699AdjacentCores/Reg.D5.S3.Arith.Erdos699AdjacentCores.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration,
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
    (fun _ _ n => ((n - 1) * (n - 2)) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Erdos699AdjacentCores, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Erdos699AdjacentCores, declaration := `D5.S3.Arith.Erdos699AdjacentCores.adjacent_core_numerator_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.observationFact0, `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699AdjacentCores


noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Erdos699AdjacentCores.arena
noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Erdos699AdjacentCores.arena
noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Erdos699AdjacentCores.arena) (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration).actual

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"adjacent_core_numerator_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Erdos699AdjacentCores, declaration := `D5.S3.Arith.Erdos699AdjacentCores.adjacent_core_numerator_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration).bridge

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.observation0 : (n M t R₁ R₂ δ₁ δ₂ : Nat) →
  (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t) →
    (hhalf :
        @LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
          M) →
      (hcop : Nat.Coprime R₁ R₂) →
        (hfirst :
            @Dvd.dvd.{0} Nat Nat.instDvd R₁
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) t
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) M t))) →
          (hsecond :
              @Dvd.dvd.{0} Nat Nat.instDvd R₂
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) t
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) M t))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) M
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)))) →
            (hδ₁ : @LE.le.{0} Nat instLENat δ₁ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
              (hδ₂ : @LE.le.{0} Nat instLENat δ₂ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                (hn₁ :
                    @Eq.{1} Nat n
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) δ₁ R₁)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (hn₂ :
                      @Eq.{1} Nat n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) δ₂)
                            R₂)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Arith.Erdos699AdjacentCores.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n M t R₁ R₂ δ₁ δ₂ : Nat)
    (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
    (hhalf :
      @LT.lt.{0} Nat instLTNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
        M)
    (hcop : Nat.Coprime R₁ R₂)
    (hfirst :
      @Dvd.dvd.{0} Nat Nat.instDvd R₁
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) t
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) M t)))
    (hsecond :
      @Dvd.dvd.{0} Nat Nat.instDvd R₂
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) t
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) M t))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) M
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t))))
    (hδ₁ : @LE.le.{0} Nat instLENat δ₁ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (hδ₂ : @LE.le.{0} Nat instLENat δ₂ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (hn₁ :
      @Eq.{1} Nat n
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) δ₁ R₁)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (hn₂ :
      @Eq.{1} Nat n
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) δ₂)
            R₂)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Erdos699AdjacentCores.signature Reg.D5.S3.Arith.Erdos699AdjacentCores.actual PUnit.unit.{1}
    PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"adjacent_core_numerator_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Erdos699AdjacentCores, declaration := `D5.S3.Arith.Erdos699AdjacentCores.adjacent_core_numerator_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"adjacent_core_numerator_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Erdos699AdjacentCores, declaration := `D5.S3.Arith.Erdos699AdjacentCores.adjacent_core_numerator_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration).actual (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration).variation.2.choose (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration).variation.1 (Reg.D5.S3.Arith.Erdos699AdjacentCores.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Erdos699AdjacentCores\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Erdos699AdjacentCores, declaration := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
