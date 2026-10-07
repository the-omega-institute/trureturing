import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
open _root_.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := (r : ℕ) × (Fin r → Type)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => sharpWidth p.2 m rhoPosition) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ} (_hr : 1 ≤ r) (h : ℕ) (hh : h ≤ r)
    (D : Fin r → Type) [∀ i, Finite (D i)] [∀ i, Nonempty (D i)],
    (∀ (A B Z O : Type) [Finite A] [Finite B] [Finite Z] [Finite O]
      [Nonempty A] [Nonempty B] [Nonempty O]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O) (b₀ : B),
      Function.Surjective (fun a => ψ a b₀) →
      width (Alphabet A B D) (task ψ G) rhoPosition ≤
        width (Alphabet A B D) (task ψ G) (piPosition h) ^ (2^h)) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∀ k : Fin (2*r+3), sharpCapacity D m (piPosition h) k.val = piCount r h m k.val) ∧
      (∀ k : Fin (2*r+3), sharpCapacity D m rhoPosition k.val = rhoCount r m k.val) ∧
      sharpWidth D m (piPosition h) = 2^h*m^(2^(r-h)) ∧
      R.readout () ⟨r,D⟩ m = m^(2^r)) ∧
    (∀ α C : ℝ, α < (2:ℝ)^h → 0<C → ∃ m : ℕ, 2 ≤ m ∧
      C * (sharpWidth D m (piPosition h) : ℝ)^α < (sharpWidth D m rhoPosition : ℝ)) ∧
    (∀ (A B Z O : Type) [Finite A] [Finite B] [Finite Z] [Finite O]
      [Nonempty A] [Nonempty B] (ψ : A → B → Z) (o : O),
      width (Alphabet A B D) (task ψ (fun _ _ => o)) (piPosition h) = 1 ∧
      width (Alphabet A B D) (task ψ (fun _ _ => o)) rhoPosition = 1 ∧
      ∀ C : ℝ,
        (width (Alphabet A B D) (task ψ (fun _ _ => o)) rhoPosition : ℝ) ≤
          C * (width (Alphabet A B D) (task ψ (fun _ _ => o)) (piPosition h) : ℝ)^(2^h : ℕ) →
        1 ≤ C)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := ((h (r := 1) (by decide) 0 (by decide) (fun _ => Unit)).2.1 2 (by decide)).2.2.2
  change (0 : ℕ) = 2^(2^1) at bad
  norm_num at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    refine ⟨⟨1, fun _ => Unit⟩, (2 : ℕ), (3 : ℕ), ?_⟩
    change sharpWidth (fun _ : Fin 1 => Unit) 2 rhoPosition ≠
      sharpWidth (fun _ : Fin 1 => Unit) 3 rhoPosition
    have two := ((result (r := 1) (by decide) 0 (by decide) (fun _ => Unit)).2.1 2 (by decide)).2.2.2
    have three := ((result (r := 1) (by decide) 0 (by decide) (fun _ => Unit)).2.1 3 (by decide)).2.2.2
    rw [two, three]
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ p m => sharpWidth p.2 m rhoPosition) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "SurjectiveColumnSharpWidth") "result") "Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth/Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ p m => sharpWidth p.2 m rhoPosition) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, definition := none, coordinates := #[0, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "arg", "arg", "arg", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.observationFact0, `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth


noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{1, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
      Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.actual)
    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration)

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{1, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.arena
    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.actual)
  Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration)

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.observation0 : {r : Nat} →
  (_hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) →
    (h : Nat) →
      (hh : @LE.le.{0} Nat instLENat h r) →
        (D : Fin r → Type) →
          [∀ (i : Fin r), Finite.{1} (D i)] →
            [∀ (i : Fin r), Nonempty.{1} (D i)] →
              (m : Nat) →
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.signature PUnit.unit.{1}
                    (@Sigma.mk.{0, 1} Nat (fun (r : Nat) => Fin r → Type) r D) :=
  fun {r : Nat} (_hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) (h : Nat)
    (hh : @LE.le.{0} Nat instLENat h r) (D : Fin r → Type) [∀ (i : Fin r), Finite.{1} (D i)]
    [∀ (i : Fin r), Nonempty.{1} (D i)] (m : Nat)
    (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.signature
    Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 1} Nat (fun (r : Nat) => Fin r → Type) r D) m

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .body, .body, .argument, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration).actual (Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration).variation.2.choose (Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration).variation.1 (Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"SurjectiveColumnSharpWidth\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth, declaration := `Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
