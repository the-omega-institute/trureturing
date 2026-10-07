import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Reg.Support.DependentFamily

open _root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open _root_.D5.S0.Computability.Coding.PrefixFreeCode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ENNReal

namespace Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ α : Type u, α → ℝ
  State := fun p => Set (List p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p F => codeMass p.2 F) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete source telescope and both local lets are retained. Only the
terminal total mass observation is replaced. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (_hp : ∀ a, 0 < p a) (_hsum : ∑ a, p a = 1)
    (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List α)),
    let o := fun n => priority p (tie n)
    let G := greedyCode o b
    Legal b G ∧
    (∀ N, IsGreatest {x : ℝ | ∃ F, Legal b F ∧
        (∀ v ∈ F, v.length ≤ N) ∧ x = truncatedMass p F N}
      (truncatedMass p G N)) ∧
    IsGreatest {x : ℝ≥0∞ | ∃ F, Legal b F ∧ x = codeMass p F}
      (R.readout () ⟨α, p⟩ G)

theorem singleton_legal {α : Type u} [Fintype α] [DecidableEq α] (a : α) :
    Legal (fun _ => 1) ({[a]} : Set (List α)) := by
  classical
  refine ⟨?_, by simp, ?_⟩
  · intro v hv w hw _
    simpa using (Set.mem_singleton_iff.mp hv).trans (Set.mem_singleton_iff.mp hw).symm
  · intro n
    have hs : level ({[a]} : Set (List α)) n ⊆ ({[a]} : Finset (List α)) := by
      intro v hv
      have hm : v ∈ ({[a]} : Set (List α)) := by
        exact ((@Finset.mem_filter (List α)
          (fun w => w ∈ ({[a]} : Set (List α)))
          (fun _ => Classical.propDecidable _) (words n) v).mp hv).2
      exact Finset.mem_singleton.mpr (Set.mem_singleton_iff.mp hm)
    simpa using Finset.card_le_card hs

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let a : ULift.{u} Unit := ⟨()⟩
  have hh := h (α := ULift.{u} Unit) (fun _ => 1) (by intro _; norm_num)
    (by simp) (fun _ => 1) (fun _ => inferInstance)
  have hmass : codeMass (fun _ : ULift.{u} Unit => 1)
      ({[a]} : Set (List (ULift.{u} Unit))) = 1 := by
    simp [codeMass, wordMass]
  have he := hh.2.2.2 (show (1 : ℝ≥0∞) ∈
      {x | ∃ F, Legal (fun _ => 1) F ∧ x = codeMass (fun _ : ULift.{u} Unit => 1) F} from
    ⟨{[a]}, singleton_legal a, hmass.symm⟩)
  change (1 : ℝ≥0∞) ≤ 0 at he
  exact not_le_of_gt zero_lt_one he

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨depth_budget_iid_greedy_optimality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, fun _ => 1⟩, ∅, {[]}, ?_⟩
    simp [actual, realize, codeMass, wordMass]

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1}
    (fun _ p F => codeMass.{u_1} p.2 F) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "Computability") "Coding") "DepthBudgetIidGreedyOptimality") "depth_budget_iid_greedy_optimality") "Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality/Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1}
    (fun _ p F => codeMass.{u_1} p.2 F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.sourceBridgeFact, `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.observationFact0, `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality


noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
      Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
      Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.actual.{u_1})
    Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1})

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"depth_budget_iid_greedy_optimality\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
    Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.actual.{u_1})
  Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1})

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.observation0.{u_1} : {α : Type u_1} →
  [inst : Fintype.{u_1} α] →
    [DecidableEq.{u_1 + 1} α] →
      (p : α → Real) →
        (hp :
            ∀ (a : α),
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (p a)) →
          (hsum :
              @Eq.{1} Real
                (@Finset.sum.{u_1, 0} α Real Real.instAddCommMonoid (@Finset.univ.{u_1} α inst) fun (a : α) => p a)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (b : Nat → Nat) →
              (tie : Nat → LinearOrder.{u_1} (List.{u_1} α)) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, 0, 0}
                  Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.signature.{u_1} PUnit.unit.{1}
                  (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (α : Type u_1) => α → Real) α p) :=
  fun {α : Type u_1} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] (p : α → Real)
    (hp :
      ∀ (a : α),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (p a))
    (hsum :
      @Eq.{1} Real (@Finset.sum.{u_1, 0} α Real Real.instAddCommMonoid (@Finset.univ.{u_1} α inst) fun (a : α) => p a)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (b : Nat → Nat) (tie : Nat → LinearOrder.{u_1} (List.{u_1} α)) =>
  have o : (n : Nat) → LinearOrder.{u_1} (List.{u_1} α) := fun (n : Nat) =>
    @D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.priority.{u_1} α p (tie n);
  have G : Set.{u_1} (List.{u_1} α) :=
    @D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.greedyCode.{u_1} α inst inst_1 o b;
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.signature.{u_1}
    Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (α : Type u_1) => α → Real) α p) G

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"depth_budget_iid_greedy_optimality\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"depth_budget_iid_greedy_optimality\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}).actual (Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}).variation.2.choose (Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}).variation.1 (Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"DepthBudgetIidGreedyOptimality\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
