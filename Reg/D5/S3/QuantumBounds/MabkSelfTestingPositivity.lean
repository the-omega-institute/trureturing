import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.MabkSelfTestingPositivity
import Reg.Support.DependentFamily

open _root_.D5.S3.QuantumBounds.MabkSelfTestingPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Classical

noncomputable section
namespace Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity

abbrev signature : Signature where
  Params := Σ n : ℕ, Finset (Fin n)
  State := fun p => Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => lambdaA p.1 p.2 v) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 6 ≤ n → ∀ T : Finset (Fin n),
    (T.card = 1 ∨ T.card = 2) → ∀ v : Fin n → ℝ,
    (∀ i, 0 ≤ v i ∧ v i ≤ kappa) → 0 ≤ R.readout () ⟨n, T⟩ v

theorem zero_cube : ∀ i : Fin 6, 0 ≤ (0 : Fin 6 → ℝ) i ∧ (0 : Fin 6 → ℝ) i ≤ kappa := by
  have hr : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro i
  constructor
  · norm_num
  · change 0 ≤ 1 - 1 / Real.sqrt 2
    have := (div_le_one hr0).mpr hr
    linarith

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 6 (by norm_num) {0} (Or.inl (by simp)) 0 zero_cube
  norm_num [rejected, realize] at hb

private def sample : Fin 6 → ℝ := fun i => if i = 0 then 1 else 0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨6, {0}⟩, 0, sample, ?_⟩
  have hJ : ({0} : Finset (Fin 6))ᶜ.Nonempty := by
    refine ⟨1, ?_⟩
    simp
  have hsample (j : Fin 6) (hj : j ∈ ({0} : Finset (Fin 6))ᶜ) : sample j = 0 := by
    simp only [mem_compl, mem_singleton] at hj
    simp [sample, hj]
  have hzero (f : ℝ → ℝ) :
      (∏ j ∈ ({0} : Finset (Fin 6))ᶜ, f (sample j)) = ∏ _j ∈ ({0} : Finset (Fin 6))ᶜ, f 0 :=
    prod_congr rfl fun j hj => congrArg f (hsample j hj)
  have hfull : (∏ j : Fin 6, sample j * (1 - ((1 + Real.sqrt 2) / Real.sqrt 2) * sample j)) = 0 := by
    apply prod_eq_zero (mem_univ (1 : Fin 6))
    norm_num [sample]
  have h1 : lambdaA 6 {0} (0 : Fin 6 → ℝ) = 1 := by
    simp [lambdaA, prod_const, card_compl]
  have h2 : lambdaA 6 {0} sample = 2 + Real.sqrt 2 := by
    let c := (1 + Real.sqrt 2) / Real.sqrt 2
    have hA : (∏ j ∈ ({0} : Finset (Fin 6))ᶜ, (1 - c * sample j)) = 1 := by
      apply prod_eq_one
      intro j hj
      rw [hsample j hj]
      ring
    have hX : (∏ j ∈ ({0} : Finset (Fin 6))ᶜ, (1 - sample j) ^ 2) = 1 := by
      apply prod_eq_one
      intro j hj
      rw [hsample j hj]
      norm_num
    have hAX : (∏ j ∈ ({0} : Finset (Fin 6))ᶜ,
        (1 - c * sample j) * (1 - sample j)) = 1 := by
      apply prod_eq_one
      intro j hj
      rw [hsample j hj]
      ring
    dsimp only [lambdaA]
    rw [hfull]
    simp only [prod_singleton]
    simp_rw [hzero]
    rw [hA, hX, hAX]
    norm_num [sample, prod_const, card_compl]
    have hr : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith only [hr2]
  change lambdaA 6 {0} 0 ≠ lambdaA 6 {0} sample
  rw [h1, h2]
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  linarith

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity
  definition := some {
    owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity
    name := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim }
  coordinates := #[0, 2]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "arg"]
    stateBinder := 4 }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.QuantumBounds.MabkSelfTestingPositivity.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p v => lambdaA p.1 p.2 v) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "QuantumBounds") "MabkSelfTestingPositivity") "result") "Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity/Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p v => lambdaA p.1 p.2 v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, definition := some { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, name := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim, path := #[] }, coordinates := #[0, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalArenaFact, `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.sourceBridgeFact, `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.observationFact0, `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity


noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.arena
noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.arena
noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.arena D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim
    Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration)

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.arena D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim
  Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration)

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.observation0 : (n : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n →
    (T : Finset.{0} (Fin n)) →
      Or (@Eq.{1} Nat (@Finset.card.{0} (Fin n) T) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (@Finset.card.{0} (Fin n) T) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        (v : Fin n → Real) →
          (∀ (i : Fin n),
              And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (v i))
                (@LE.le.{0} Real Real.instLE (v i) D5.S3.QuantumBounds.MabkSelfTestingPositivity.kappa)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat (fun (n : Nat) => Finset.{0} (Fin n)) n T) :=
  fun (n : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n)
    (T : Finset.{0} (Fin n))
    (a_1 :
      Or (@Eq.{1} Nat (@Finset.card.{0} (Fin n) T) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat (@Finset.card.{0} (Fin n) T) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (v : Fin n → Real)
    (a_2 :
      ∀ (i : Fin n),
        And
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (v i))
          (@LE.le.{0} Real Real.instLE (v i) D5.S3.QuantumBounds.MabkSelfTestingPositivity.kappa)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.signature Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.actual
    PUnit.unit.{1} (@Sigma.mk.{0, 0} Nat (fun (n : Nat) => Finset.{0} (Fin n)) n T) v

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim, part := .value, path := [.body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration).actual (Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration).variation.2.choose (Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration).variation.1 (Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumBounds\",\"MabkSelfTestingPositivity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity, declaration := `Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
