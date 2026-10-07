import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.ReferencePrefixDominance
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance

open Finset
open _root_.D5.S3.Arith.GoldenResource.ReferencePrefixDominance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Only the harmonic summand varies; the complete source
telescope and geometric-prefix logarithm remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law := fun r => ∀ {z : ℝ} {a : ℕ},
    1 ≤ a → 0 < z → z < 1 →
    Real.log (∑ k ∈ range (a + 1), z ^ k) <
      ∑ k ∈ range a, r.readout () ⟨z, a⟩ k

def actual : Realization signature :=
  realize signature (fun _ p k => p.1 ^ (k + 1) / (k + 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0)
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h (z := (1 / 2 : ℝ)) (a := 1)
    (by decide) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hfalse
  exact (not_lt_of_ge (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).le) hfalse

def registration : Registration arena
    (∀ {z : ℝ} {a : ℕ}, 1 ≤ a → 0 < z → z < 1 →
      Real.log (∑ k ∈ range (a + 1), z ^ k) <
        ∑ k ∈ range a, z ^ (k + 1) / (k + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨log_geom_prefix_lt_harmonic_prefix, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(1 / 2 : ℝ), 2⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p k => p.1 ^ (k + 1) / (k + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "GoldenResource") "ReferencePrefixDominance") "log_geom_prefix_lt_harmonic_prefix") "Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance/Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration,
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
    (fun _ p k => p.1 ^ (k + 1) / (k + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.observationFact0, `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance


noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.arena
noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.arena
noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.arena
    (∀ {z : Real} {a : Nat},
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z →
          @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LT.lt.{0} Real Real.instLT
              (Real.log
                (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
                  (Finset.range
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  fun (k : Nat) =>
                  @HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z k))
              (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range a) fun (k : Nat) =>
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast k)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
    Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration)

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"log_geom_prefix_lt_harmonic_prefix\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.arena
  (∀ {z : Real} {a : Nat},
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z →
        @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
          @LT.lt.{0} Real Real.instLT
            (Real.log
              (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
                (Finset.range
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                fun (k : Nat) =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z k))
            (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range a) fun (k : Nat) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast k)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration)

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.observation0 : {z : Real} →
  {a : Nat} →
    (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a) →
      (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z) →
        (hz1 :
            @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.signature
              (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) z a) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) z a) :=
  fun {z : Real} {a : Nat} (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
    (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
    (hz1 : @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.signature
    Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) z a)

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"log_geom_prefix_lt_harmonic_prefix\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix, part := .type, path := [.body, .body, .body, .body, .body, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"log_geom_prefix_lt_harmonic_prefix\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration).actual (Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration).variation.2.choose (Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration).variation.1 (Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ReferencePrefixDominance\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance, declaration := `Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
