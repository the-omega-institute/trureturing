import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Prediction.BoundedRationalReadout
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Prediction.BoundedRationalReadout

open _root_.D5.S3.Observer.Prediction.BoundedRationalReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => balanceBits (balance w)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)

noncomputable def arena : Arena where
  signature := signature
  Law R :=
    ∀ (K : ℕ) (_hK : 1 ≤ K) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1 / 4)
    (_hδ : tailError K ≤ ε),
    (∀ b : ℤ, exactReadout (-b) = 1 - exactReadout b) ∧
    (∀ b : ℤ, (K : ℤ) ≤ b →
      3 / 4 - exactReadout b = 1 / (2 * (1 + (3 : ℝ) ^ b)) ∧
      0 ≤ 3 / 4 - exactReadout b ∧ 3 / 4 - exactReadout b ≤ tailError K) ∧
    (∀ b : ℤ, b ≤ -(K : ℤ) →
      exactReadout b - 1 / 4 = 1 / (2 * (1 + (3 : ℝ) ^ (-b))) ∧
      0 ≤ exactReadout b - 1 / 4 ∧ exactReadout b - 1 / 4 ≤ tailError K) ∧
    (∀ w : List Bool, |clippedReadout K (balance w) - exactReadout (balance w)| ≤ ε) ∧
    (∀ b : ℤ, 0 < (outputFraction K b).2 ∧
      ((outputFraction K b).1 : ℝ) / (outputFraction K b).2 = clippedReadout K b ∧
      (outputFraction K b).1.bits.length ≤ 2 * K + 4 ∧
      (outputFraction K b).2.bits.length ≤ 2 * K + 4) ∧
    (∀ i : Fin (2 * K - 1),
      0 < (interiorTable K i).2 ∧
      ((interiorTable K i).1 : ℝ) / (interiorTable K i).2 =
        exactReadout ((i.val : ℤ) - ((K : ℤ) - 1)) ∧
      (interiorTable K i).1 < 2 ^ (2 * K + 4) ∧
      (interiorTable K i).2 < 2 ^ (2 * K + 4)) ∧
    tableBits K ≤ 24 * K ^ 2 ∧
    balance [] = 0 ∧
    (∀ (w : List Bool) (x : Bool),
      balance (w ++ [x]) = balance w + (if x then 1 else -1)) ∧
    (∀ w : List Bool,
      balance w = (w.count true : ℤ) - w.count false ∧
      (balance w).natAbs ≤ w.length ∧
      R.readout () () w ≤ 2 + Nat.log2 (w.length + 1)) ∧
    (¬ ∃ forecast : ℕ → ℝ → ℕ → ℝ, ∀ (w : List Bool) (n : ℕ),
      |forecast w.length (clippedReadout K (balance w)) n -
        exactReadout (balance w - (n : ℤ))| ≤ ε) ∧
    ¬ ∃ update : ℝ → Bool → ℝ, ∀ (b : ℤ) (x : Bool),
      update (clippedReadout K b) x =
        clippedReadout K (b + (if x then 1 else -1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 le_rfl (1 / 8) (by norm_num) (by norm_num)
    (by norm_num [tailError])).2.2.2.2.2.2.2.2.2.1 []
  have hn : ¬ (100 : ℕ) ≤ 2 + Nat.log2 1 := by decide
  exact hn hh.2.2

noncomputable def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_tail_clip_error_and_bit_budget, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), [], [true], ?_⟩
    change (1 : ℕ) ≠ 2
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Prediction.BoundedRationalReadout.uniform_tail_clip_error_and_bit_budget) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => balanceBits (balance w))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Prediction") "BoundedRationalReadout") "uniform_tail_clip_error_and_bit_budget") "Reg.D5.S3.Observer.Prediction.BoundedRationalReadout/Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => balanceBits (balance w))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Prediction.BoundedRationalReadout, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg", "arg", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `D5.S3.Observer.Prediction.BoundedRationalReadout.uniform_tail_clip_error_and_bit_budget, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.observationFact0, `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Observer.Prediction.BoundedRationalReadout


noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
      Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.actual)
    Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration)

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"uniform_tail_clip_error_and_bit_budget\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `D5.S3.Observer.Prediction.BoundedRationalReadout.uniform_tail_clip_error_and_bit_budget, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.arena
    Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.actual)
  Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration)

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.observation0 : (K : Nat) →
  (hK : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) K) →
    (ε : Real) →
      (_hε :
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε) →
        (_hε' :
            @LT.lt.{0} Real Real.instLT ε
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) →
          (hδ : @LE.le.{0} Real Real.instLE (D5.S3.Observer.Prediction.BoundedRationalReadout.tailError K) ε) →
            (w : List.{0} Bool) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (K : Nat) (hK : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) K) (ε : Real)
    (_hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (_hε' :
      @LT.lt.{0} Real Real.instLT ε
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
    (hδ : @LE.le.{0} Real Real.instLE (D5.S3.Observer.Prediction.BoundedRationalReadout.tailError K) ε)
    (w : List.{0} Bool) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.signature
    Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.actual PUnit.unit.{1} PUnit.unit.{1} w

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"uniform_tail_clip_error_and_bit_budget\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `D5.S3.Observer.Prediction.BoundedRationalReadout.uniform_tail_clip_error_and_bit_budget, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .body, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"uniform_tail_clip_error_and_bit_budget\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `D5.S3.Observer.Prediction.BoundedRationalReadout.uniform_tail_clip_error_and_bit_budget, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration).actual (Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration).variation.2.choose (Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration).variation.1 (Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Prediction\",\"BoundedRationalReadout\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout, declaration := `Reg.D5.S3.Observer.Prediction.BoundedRationalReadout.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
