import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold

open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => goldenLucas n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law x := ∀ (r n : ℕ) (_hr : 119 ≤ r) (_hn : 2 * r + 1 ≤ n),
    128 * (6 : ℤ) ^ r + 4 < (x.readout () r n) ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 119 239 (by decide) (by decide)
  change (128 : ℤ) * 6 ^ 119 + 4 < (0 : ℤ) ^ 2 at hbad
  have hpos : 0 < (6 : ℤ) ^ 119 := pow_pos (by norm_num) _
  nlinarith

def registration : Registration arena
    (∀ (r n : ℕ) (_hr : 119 ≤ r) (_hn : 2 * r + 1 ≤ n),
      128 * (6 : ℤ) ^ r + 4 < goldenLucas n ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_lucas_nonsquare_threshold, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨0, (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas 0 ≠ goldenLucas 1
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => goldenLucas n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "GoldenLucasNonsquareThreshold") "golden_lucas_nonsquare_threshold") "Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold/Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => goldenLucas n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold


noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena
    (∀ (r n : Nat) (_hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r)
      (_hn :
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          n),
      @LT.lt.{0} Int Int.instLTInt
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 128) (@instOfNat (nat_lit 128)))
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))) r))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
        (@HPow.hPow.{0, 0, 0} Int Nat Int
          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
          (D5.S1.Scale.goldenLucas n) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"golden_lucas_nonsquare_threshold\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena
  (∀ (r n : Nat) (_hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r)
    (_hn :
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        n),
    @LT.lt.{0} Int Int.instLTInt
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 128) (@instOfNat (nat_lit 128)))
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))) r))
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
        (D5.S1.Scale.goldenLucas n) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.observation0 : (r n : Nat) →
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r) →
    (hn :
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          n) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.signature PUnit.unit.{1} r :=
  fun (r n : Nat) (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r)
    (hn :
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.signature
    Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.actual PUnit.unit.{1} r n

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"golden_lucas_nonsquare_threshold\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold, part := .type, path := [.body, .body, .body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"golden_lucas_nonsquare_threshold\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration).actual (Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration).variation.1 (Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenLucasNonsquareThreshold\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, declaration := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
