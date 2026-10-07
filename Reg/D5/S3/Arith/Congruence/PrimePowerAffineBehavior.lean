import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.PrimePowerAffineBehavior
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Congruence.PrimePowerAffineBehavior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior

@[reducible] def signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := (ℕ × ZMod (q.1 ^ (q.2.1 - q.2.2))) ⊕
    ZMod (q.1 ^ (q.2.1 - q.2.2))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q x => eta q.1 q.2.1 q.2.2 x) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ q _ => eta q.1 q.2.1 q.2.2 2) (fun z => nomatch z)

/-- The complete original telescope and all its clauses. The sole intervention
is the left coordinate in the positive affine classification equivalence. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p h e : ℕ) (_hp : p.Prime) (_he : e ≤ h),
    (∀ x : ℤ, depth p h x ≤ h ∧
      Int.gcd x ((p : ℤ) ^ h) = p ^ depth p h x ∧
      (depth p h x = h ↔ (p : ℤ) ^ h ∣ x) ∧
      (x ≠ 0 → depth p h x = min (padicValInt p x) h) ∧
      (depth p h x < e → IsUnit ((x / (p : ℤ) ^ depth p h x : ℤ) :
        ZMod (p ^ (h - e))))) ∧
    (∀ x y : ℤ, Int.ModEq ((p : ℤ) ^ h) x y →
      depth p h x = depth p h y ∧ eta p h e x = eta p h e y) ∧
    (∀ x : ℤ, ∃ X : ℤ, 0 < X ∧ Int.ModEq ((p : ℤ) ^ h) x X) ∧
    (∀ a b : ℤ, ∃ A B : ℤ, 0 < A ∧ 0 ≤ B ∧
      ∀ x : ℤ, Int.ModEq ((p : ℤ) ^ h)
        (a * x + (p : ℤ) ^ e * b) (A * x + (p : ℤ) ^ e * B)) ∧
    (∀ w : List (ℕ+ ⊕ Unit), ∃ A B : ℕ, 0 < A ∧
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B) ∧
    (∀ A B : ℕ, 0 < A → ∃ w : List (ℕ+ ⊕ Unit),
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B) ∧
    (∀ x y : ℤ, (R.readout () ⟨p, ⟨h, e⟩⟩ x = eta p h e y ↔
      ∀ a b : ℤ, 0 < a → 0 ≤ b →
        depth p h (a * x + (p : ℤ) ^ e * b) =
        depth p h (a * y + (p : ℤ) ^ e * b)) ∧
      (eta p h e x = eta p h e y ↔
        ∀ w : List (ℕ+ ⊕ Unit), depth p h (run p e w x) = depth p h (run p e w y))) ∧
    (e = h → ∀ u v : (ZMod (p ^ (h - e)))ˣ, u = v)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (((h 2 1 0 (by decide) (by omega)).2.2.2.2.2.2.1 1 1).1).mpr
    (fun a b ha hb => rfl)
  change eta 2 1 0 (2 : ℤ) = eta 2 1 0 (1 : ℤ) at bad
  exact (by decide : eta 2 1 0 (2 : ℤ) ≠ eta 2 1 0 (1 : ℤ)) bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨local_classification, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, ⟨1, 0⟩⟩, 2, 1, ?_⟩
    change eta 2 1 0 (2 : ℤ) ≠ eta 2 1 0 (1 : ℤ)
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.local_classification) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q x => eta q.1 q.2.1 q.2.2 x) (fun z => nomatch z))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Congruence") "PrimePowerAffineBehavior") "local_classification") "Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior/Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration,
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
    (fun _ q x => eta q.1 q.2.1 q.2.2 x) (fun z => nomatch z)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior.local_classification, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.observationFact0, `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior


noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.arena
noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.arena
noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.arena) (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration).actual

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"local_classification\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior.local_classification, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration).bridge

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.observation0 : (p h e : Nat) →
  (hp : Nat.Prime p) →
    (he : @LE.le.{0} Nat instLENat e h) →
      (x y : Int) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat) p
            (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) h e)) :=
  fun (p h e : Nat) (hp : Nat.Prime p) (he : @LE.le.{0} Nat instLENat e h) (x y : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.signature
    Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat) p
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) h e))
    x

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"local_classification\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior.local_classification, part := .type, path := [.body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .body, .body, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"local_classification\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior.local_classification, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration).actual (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration).variation.2.choose (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration).variation.1 (Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"PrimePowerAffineBehavior\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior, declaration := `Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
